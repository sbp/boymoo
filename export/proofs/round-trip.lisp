; A printed line, with its line feed, reads as its word and its data.

(in-package "ACL2")

(include-book "round-trip-atoms")

; A word consists of at least one lowercase letter or hyphen.
(defun rt-word-char-p (c)
  (and (characterp c)
       (or (equal (char-code c) 45)
           (and (<= 97 (char-code c)) (<= (char-code c) 122)))))

(defun rt-word-chars-p (cs)
  (if (consp cs)
      (and (rt-word-char-p (car cs)) (rt-word-chars-p (cdr cs)))
    (equal cs nil)))

(defun rt-word-p (word)
  (and (stringp word)
       (consp (coerce word 'list))
       (rt-word-chars-p (coerce word 'list))))

(defun rt-word-admitted-p (word words)
  (consp (boymoo::pair-of (coerce word 'list) words)))

; Write a datum and its enclosing list in the order the reader sees
; them. Each function leaves the given suffix of the line after its text.
(mutual-recursion
 (defun rt-object-text (x rest)
   (if (consp x)
       (cons #\( (rt-object-text (car x) (rt-tail-text (cdr x) rest)))
     (append (rt-atom-text x) rest)))
 (defun rt-tail-text (x rest)
   (cond ((consp x)
          (cons #\Space (rt-object-text (car x) (rt-tail-text (cdr x) rest))))
         ((null x) (cons #\) rest))
         (t (list* #\Space #\. #\Space
                    (append (rt-atom-text x) (cons #\) rest)))))))

(defun rt-arguments-text (args rest)
  (if (consp args)
      (cons #\Space (rt-object-text (car args)
                                  (rt-arguments-text (cdr args) rest)))
    rest))

; Undo the reversal of the printer. The induction follows its
; accumulator and the suffix of the forward text at the same time.
(local
 (defun rt-printer-induction (tailp x acc rest)
   (if (consp x)
       (let ((start (cons (if tailp #\Space #\() acc)))
         (list (rt-printer-induction nil (car x) start
                                     (rt-tail-text (cdr x) rest))
               (rt-printer-induction t (cdr x) (bm-obj (car x) start)
                                     rest)))
     (list tailp x acc rest))))

(local
 (defthm rt-printer-forward
   (implies (rt-format-datum-p x)
            (if tailp
                (equal (revappend (bm-tail x acc) rest)
                       (revappend acc (rt-tail-text x rest)))
              (equal (revappend (bm-obj x acc) rest)
                     (revappend acc (rt-object-text x rest)))))
   :hints (("Goal" :induct (rt-printer-induction tailp x acc rest)
            :expand ((bm-obj x acc) (bm-tail x acc)
                     (rt-object-text x rest) (rt-tail-text x rest))))
   :rule-classes nil))

(local
 (defthm rt-print-object-in-order
   (implies (rt-format-datum-p x)
            (equal (revappend (bm-obj x acc) rest)
                   (revappend acc (rt-object-text x rest))))
   :hints (("Goal" :use ((:instance rt-printer-forward (tailp nil)))))
   :rule-classes :rewrite))

(local
 (defthm rt-print-arguments-in-order
   (implies (rt-format-datum-p args)
            (equal (revappend (bm-args args acc) rest)
                   (revappend acc (rt-arguments-text args rest))))
   :hints (("Goal" :induct (bm-args args acc)
            :in-theory (disable bm-obj rt-object-text)))))

; The forward text is a character list, so the two coercions at the
; string interface recover precisely these characters.
(local
 (defun rt-text-induction (x rest)
   (if (consp x)
       (list (rt-text-induction (cdr x) rest)
             (rt-text-induction (car x) (rt-tail-text (cdr x) rest)))
     rest)))

(local
 (defthm rt-objects-and-tails-are-characters
   (implies (and (rt-format-datum-p x) (character-listp rest))
            (and (character-listp (rt-object-text x rest))
                 (character-listp (rt-tail-text x rest))))
   :hints (("Goal" :induct (rt-text-induction x rest)
            :expand ((rt-object-text x rest) (rt-tail-text x rest))))))

(local
 (defthm rt-arguments-are-characters
   (implies (and (rt-format-datum-p args) (character-listp rest))
            (character-listp (rt-arguments-text args rest)))
   :hints (("Goal" :induct (rt-arguments-text args rest)
            :in-theory (disable rt-object-text rt-tail-text)))))

(local
 (defthm rt-bm-line-characters
   (implies (rt-format-datum-p args)
            (equal (coerce (bm-line word args) 'list)
                   (cons #\( (append (coerce word 'list)
                                    (rt-arguments-text args '(#\)))))))
   :hints (("Goal" :in-theory (disable bm-args rt-arguments-text)))))

(local
 (defthm rt-text-with-trailing-characters
   (and (equal (append (rt-object-text x rest) suffix)
               (rt-object-text x (append rest suffix)))
        (equal (append (rt-tail-text x rest) suffix)
               (rt-tail-text x (append rest suffix))))
   :hints (("Goal" :induct (rt-text-induction x rest)
            :expand ((:free (rest) (rt-object-text x rest))
                     (:free (rest) (rt-tail-text x rest)))))))

(local
 (defthm rt-argument-text-with-trailing-characters
   (equal (append (rt-arguments-text args rest) suffix)
          (rt-arguments-text args (append rest suffix)))
   :hints (("Goal" :in-theory (disable rt-object-text rt-tail-text)
            :expand ((:free (rest) (rt-arguments-text args rest)))))))

(defthm rt-bm-line-with-trailing-characters
  (implies (rt-format-datum-p args)
           (equal (append (coerce (bm-line word args) 'list) rest)
                  (cons #\( (append (coerce word 'list)
                                    (rt-arguments-text args (cons #\) rest))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable bm-line rt-arguments-text))))

; Advance the parser through a datum, or through the tail of an open
; list. A frame records the elements already seen, in reverse order.
(local
 (defun rt-datum-boundary-p (rest)
   (and (consp rest)
        (or (equal (car rest) #\Space) (equal (car rest) #\))))))

(local
 (defthm rt-datum-boundary-is-atom-boundary
   (implies (rt-datum-boundary-p rest) (rt-atom-boundary-p rest))
   :hints (("Goal" :in-theory (enable rt-atom-boundary-p rt-plain-char-p)))))

(local
 (defthm rt-tail-has-datum-boundary
   (rt-datum-boundary-p (rt-tail-text x rest))
   :hints (("Goal" :expand ((rt-tail-text x rest))))))

(local
 (defthm rt-arguments-have-datum-boundary
   (implies (rt-datum-boundary-p rest)
            (rt-datum-boundary-p (rt-arguments-text args rest)))))

(local
 (defthm rt-atom-frame
   (implies (and (rt-format-datum-p x) (not (consp x))
                 (rt-written-symbols-pass-index-p x pkgs)
                 (rt-datum-boundary-p rest))
            (equal (boymoo::parse-loop (append (rt-atom-text x) rest) stack t pkgs)
                   (boymoo::parse-loop rest
                                      (cons (cons (rt-datum-form x) (car stack))
                                            (cdr stack))
                                      nil pkgs)))
   :hints (("Goal" :use rt-lex-atom-of-text
            :in-theory (disable rt-datum-boundary-p rt-datum-form
                                boymoo::parse-loop rt-lex-atom-of-text)
            :expand ((boymoo::parse-loop (append (rt-atom-text x) rest)
                                         stack t pkgs))))))

(local
 (defthm rt-object-does-not-start-with-tail-marker
   (implies (and (rt-format-datum-p x)
                 (rt-written-symbols-pass-index-p x pkgs)
                 (rt-datum-boundary-p rest))
            (not (and (equal (car (rt-object-text x rest)) #\.)
                      (equal (cadr (rt-object-text x rest)) #\Space))))
   :hints (("Goal" :expand ((rt-object-text x rest))
            :use rt-lex-atom-of-text
            :in-theory (disable rt-datum-boundary-p rt-datum-form
                                rt-lex-atom-of-text)
            :do-not-induct t))))

(local
 (defthm rt-form-of-non-nil
   (implies (rt-format-datum-p x)
            (iff (rt-datum-form x) x))
   :hints (("Goal" :use ((:instance rt-datum-form-injective (y nil)))
            :in-theory (disable rt-datum-form rt-datum-form-injective)))))

(local
 (defthm rt-open-list-frame
   (equal (boymoo::parse-loop (cons #\( rest) stack t pkgs)
          (boymoo::parse-loop rest (cons nil stack) t pkgs))
   :hints (("Goal" :expand ((boymoo::parse-loop (cons #\( rest) stack t pkgs))
            :in-theory (disable boymoo::parse-loop)))))

(local
 (defthm rt-close-list-frame
   (implies (consp (cdr stack))
            (equal (boymoo::parse-loop (cons #\) rest) stack nil pkgs)
                   (boymoo::parse-loop
                    rest
                    (cons (cons (revappend (car stack) nil) (cadr stack))
                          (cddr stack))
                    nil pkgs)))
   :hints (("Goal" :expand ((boymoo::parse-loop (cons #\) rest) stack nil pkgs))
            :in-theory (disable boymoo::parse-loop)))))

(local
 (defthm rt-space-before-element
   (implies (not (and (equal (car rest) #\.) (equal (cadr rest) #\Space)))
            (equal (boymoo::parse-loop (cons #\Space rest) stack nil pkgs)
                   (boymoo::parse-loop rest stack t pkgs)))
   :hints (("Goal" :expand ((boymoo::parse-loop (cons #\Space rest) stack nil pkgs))
            :in-theory (disable boymoo::parse-loop)))))

(local
 (defthm rt-close-dotted-list-frame
   (implies (and (consp (cdr stack)) (rt-format-datum-p x) (not (consp x)) x
                 (rt-written-symbols-pass-index-p x pkgs))
            (equal (boymoo::parse-loop
                    (list* #\Space #\. #\Space
                           (append (rt-atom-text x) (cons #\) rest)))
                    stack nil pkgs)
                   (boymoo::parse-loop
                    rest
                    (cons (cons (revappend (car stack) (rt-datum-form x))
                                (cadr stack))
                          (cddr stack))
                    nil pkgs)))
   :hints (("Goal" :expand ((boymoo::parse-loop
                             (list* #\Space #\. #\Space
                                    (append (rt-atom-text x) (cons #\) rest)))
                             stack nil pkgs))
            :in-theory (e/d (rt-atom-boundary-p)
                             (boymoo::parse-loop rt-datum-form))))))

; The next frame in the induction is the one produced after reading
; the next car. Its remaining cdr is the next tail.
(local
 (defun rt-parser-induction (tailp x rest stack)
   (if (consp x)
       (let ((frame (if tailp stack (cons nil stack))))
         (list (rt-parser-induction nil (car x) (rt-tail-text (cdr x) rest)
                                    frame)
               (rt-parser-induction t (cdr x) rest
                                    (cons (cons (rt-datum-form (car x))
                                                (car frame))
                                          (cdr frame)))))
     (list tailp x rest stack))))

(local
 (defthm rt-parser-advances-through-object-and-tail
   (implies (rt-format-datum-p x)
            (if tailp
                (implies (and (consp (cdr stack))
                              (or (null x) (rt-written-symbols-pass-index-p x pkgs)))
                         (equal (boymoo::parse-loop (rt-tail-text x rest) stack nil pkgs)
                                (boymoo::parse-loop
                                 rest
                                 (cons (cons (revappend (car stack) (rt-datum-form x))
                                             (cadr stack))
                                       (cddr stack))
                                 nil pkgs)))
              (implies (and (consp stack) (rt-written-symbols-pass-index-p x pkgs)
                            (rt-datum-boundary-p rest))
                       (equal (boymoo::parse-loop (rt-object-text x rest) stack t pkgs)
                              (boymoo::parse-loop
                               rest
                               (cons (cons (rt-datum-form x) (car stack)) (cdr stack))
                               nil pkgs)))))
   :hints (("Goal" :induct (rt-parser-induction tailp x rest stack)
            :in-theory (disable boymoo::parse-loop rt-datum-boundary-p
                                rt-object-text rt-tail-text)
            :expand ((rt-object-text x rest) (rt-tail-text x rest))))
   :rule-classes nil))

(local
 (defthm rt-parse-object
   (implies (and (rt-format-datum-p x) (rt-written-symbols-pass-index-p x pkgs)
                 (consp stack) (rt-datum-boundary-p rest))
            (equal (boymoo::parse-loop (rt-object-text x rest) stack t pkgs)
                   (boymoo::parse-loop rest
                                      (cons (cons (rt-datum-form x) (car stack))
                                            (cdr stack))
                                      nil pkgs)))
   :hints (("Goal" :use ((:instance rt-parser-advances-through-object-and-tail
                                     (tailp nil)))))))

; The word and the arguments share the outer frame. Unlike a datum
; list, that frame has a word even when there are no arguments.
(local
 (defun rt-arguments-induction (args rest stack)
   (if (consp args)
       (rt-arguments-induction
        (cdr args) rest
        (cons (cons (rt-datum-form (car args)) (car stack)) (cdr stack)))
     (list rest stack))))

(local
 (defthm rt-parse-arguments
   (implies (and (rt-format-datum-p args) (consp stack)
                 (or (null args) (rt-written-symbols-pass-index-p args pkgs))
                 (rt-datum-boundary-p rest))
            (equal (boymoo::parse-loop (rt-arguments-text args rest) stack nil pkgs)
                   (boymoo::parse-loop
                    rest
                    (cons (revappend (rt-datum-form args) (car stack)) (cdr stack))
                    nil pkgs)))
   :hints (("Goal" :induct (rt-arguments-induction args rest stack)
            :in-theory (disable boymoo::parse-loop rt-datum-boundary-p
                                rt-object-text rt-tail-text)))))

(local
 (defthm rt-scan-word
   (implies (and (rt-word-chars-p cs) (not (rt-word-char-p (car rest))))
            (equal (boymoo::lex-word (append cs rest) acc)
                   (cons (revappend cs acc) rest)))
   :hints (("Goal" :induct (revappend cs acc)
            :in-theory (disable rt-equal-char-codes)))))

(local
 (defthm rt-word-stops-at-datum-boundary
   (implies (rt-datum-boundary-p rest)
            (not (rt-word-char-p (car rest))))))

(local
 (defthm rt-arguments-form-true-list
   (implies (true-listp args)
            (true-listp (rt-datum-form args)))
   :rule-classes :type-prescription))

(local
 (defthm rt-close-line-frame
   (implies (not (consp (cdr stack)))
            (equal (boymoo::parse-loop (list* #\) #\Newline rest) stack nil pkgs)
                   (cons (revappend (car stack) nil) rest)))
   :hints (("Goal" :expand ((boymoo::parse-loop (list* #\) #\Newline rest)
                                                 stack nil pkgs))
            :in-theory (disable boymoo::parse-loop)))))

; An accepted word uses the tag in the word table. The line feed is
; the one that bm-write-lines writes after calling the printer.
(defthm rt-parse-printed-line-with-package-index
  (implies (and (rt-word-p word)
                (rt-word-admitted-p word words)
                (true-listp args)
                (rt-format-datum-p args)
                (or (null args) (rt-written-symbols-pass-index-p args pkgs)))
           (equal (boymoo::parse-line
                   (append (coerce (bm-line word args) 'list) '(#\Newline))
                   words pkgs)
                  (cons (cdr (boymoo::pair-of (coerce word 'list) words))
                        (rt-datum-form args))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable bm-line boymoo::lex-word
                                     boymoo::pair-of boymoo::parse-loop
                                     rt-arguments-text rt-datum-form))))
