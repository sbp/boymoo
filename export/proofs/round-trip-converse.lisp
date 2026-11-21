; A line that is read successfully can be reconstructed from what was read.

(in-package "ACL2")

(include-book "round-trip")
(include-book "round-trip-lexical")

; The text of the reader's representation uses the ordinary list syntax
; and the qualified spelling that each represented symbol carries.
(mutual-recursion
 (defun rt-reader-object-text (x rest)
   (if (consp x)
       (cons #\( (rt-reader-object-text (car x)
                                        (rt-reader-tail-text (cdr x) rest)))
     (append (rt-reader-atom-text x) rest)))
 (defun rt-reader-tail-text (x rest)
   (cond ((consp x)
          (cons #\Space (rt-reader-object-text (car x)
                                               (rt-reader-tail-text (cdr x) rest))))
         ((null x) (cons #\) rest))
         (t (list* #\Space #\. #\Space
                    (append (rt-reader-atom-text x) (cons #\) rest)))))))

(defun rt-reader-arguments-text (args rest)
  (if (consp args)
      (cons #\Space (rt-reader-object-text
                     (car args) (rt-reader-arguments-text (cdr args) rest)))
    rest))

(defun rt-reader-line-text (word args)
  (cons #\( (append (coerce word 'list)
                    (rt-reader-arguments-text args '(#\) #\Newline)))))

; The outer frame holds at least its word. An inner frame is empty only
; just after its opening parenthesis, while it needs its first element.
(local
 (defun rt-open-frames-p (stack elem)
   (and (consp stack)
        (if (consp (cdr stack))
            (and (or elem (consp (car stack)))
                 (rt-open-frames-p (cdr stack) t))
          (consp (car stack))))))

(local
 (defthm rt-open-frames-are-nonempty
   (implies (rt-open-frames-p stack elem) (consp stack))
   :rule-classes :forward-chaining))

(local
 (defun rt-frame-elements-text (items rest)
   (if (consp items)
       (rt-frame-elements-text
        (cdr items) (if (consp (cdr items))
                        (cons #\Space (rt-reader-object-text (car items) rest))
                      (rt-reader-object-text (car items) rest)))
     rest)))

(local
 (defun rt-open-frames-text (stack elem word rest)
   (if (consp (cdr stack))
       (rt-open-frames-text
        (cdr stack) t word
        (cons #\( (rt-frame-elements-text
                   (car stack)
                   (if (and elem (consp (car stack))) (cons #\Space rest) rest))))
     (cons #\( (append word
                       (rt-reader-arguments-text
                        (cdr (revappend (car stack) nil))
                        (if elem (cons #\Space rest) rest)))))))

; The text of a cons with elements read in reverse, followed by its tail.
(local
 (defthm rt-reader-object-text-of-reversed-frame
   (implies (consp items)
            (equal (rt-reader-object-text (revappend items tail) rest)
                   (cons #\( (rt-frame-elements-text
                              items (rt-reader-tail-text tail rest)))))
   :hints (("Goal" :induct (revappend items tail)
            :in-theory (disable rt-reader-object-text rt-reader-tail-text)
            :expand ((rt-reader-object-text (cons (car items) tail) rest)
                     (rt-reader-tail-text (cons (car items) tail) rest))))))

(local
 (defthm rt-arguments-text-of-append
   (equal (rt-reader-arguments-text (append x y) rest)
          (rt-reader-arguments-text x (rt-reader-arguments-text y rest)))
   :hints (("Goal" :induct (append x y)
            :in-theory (disable rt-reader-object-text)
            :expand ((:free (rest) (rt-reader-arguments-text x rest)))))))

(local
 (defthm rt-one-reader-argument
   (equal (rt-reader-arguments-text (list value) rest)
          (cons #\Space (rt-reader-object-text value rest)))))

(local
 (defthm rt-no-reader-arguments
   (equal (rt-reader-arguments-text nil rest) rest)))

(local
 (defthm rt-cdr-of-extended-frame
   (implies (consp frame)
            (equal (cdr (revappend frame (list value)))
                   (append (cdr (revappend frame nil)) (list value))))
   :hints (("Goal" :use ((:instance rt-append-of-revappend
                                     (x frame) (y nil) (z (list value))))
            :in-theory (disable rt-append-of-revappend)))))

; Opening a frame, adding a value, and shifting a space leave the
; reconstructed prefix of the line unchanged.
(local
 (defthm rt-opening-a-frame-keeps-text
   (implies (consp stack)
            (equal (rt-open-frames-text (cons nil stack) t word rest)
                   (rt-open-frames-text stack t word (cons #\( rest))))
   :hints (("Goal" :expand ((rt-open-frames-text (cons nil stack) t word rest))
            :in-theory (disable rt-open-frames-text)))))

(local
 (defthm rt-adding-a-value-keeps-text
   (implies (rt-open-frames-p stack t)
            (equal (rt-open-frames-text (cons (cons value (car stack)) (cdr stack))
                                        nil word rest)
                   (rt-open-frames-text stack t word
                                        (rt-reader-object-text value rest))))
   :hints (("Goal" :expand ((rt-open-frames-text
                             (cons (cons value (car stack)) (cdr stack)) nil word rest)
                            (rt-open-frames-text stack t word
                                                 (rt-reader-object-text value rest))
                            (rt-frame-elements-text (cons value (car stack)) rest))
            :in-theory (disable rt-open-frames-text rt-reader-object-text
                                rt-reader-arguments-text)))))

(local
 (defthm rt-shifting-a-space-keeps-text
   (implies (consp (car stack))
            (equal (rt-open-frames-text stack t word rest)
                   (rt-open-frames-text stack nil word (cons #\Space rest))))
   :hints (("Goal" :expand ((rt-open-frames-text stack t word rest)
                            (rt-open-frames-text stack nil word (cons #\Space rest)))
            :in-theory (disable rt-open-frames-text)))))

(local
 (defthm rt-closing-a-frame-keeps-text
   (implies (and (rt-open-frames-p stack nil) (consp (cdr stack)))
            (equal (rt-open-frames-text
                    (cons (cons (revappend (car stack) tail) (cadr stack))
                          (cddr stack))
                    nil word rest)
                   (rt-open-frames-text stack nil word (rt-reader-tail-text tail rest))))
   :hints (("Goal" :expand ((rt-open-frames-text stack nil word
                                                 (rt-reader-tail-text tail rest)))
            :in-theory (disable rt-open-frames-text rt-reader-tail-text
                                rt-reader-object-text)))))

; An atom's scan and the punctuation of a dotted tail give the text
; that is consumed before the parser continues in the current frame.
(local
 (defthm rt-object-text-of-scanned-atom
   (let ((r (boymoo::lex-atom cs pkgs)))
     (implies r
              (equal (rt-reader-object-text (car r) (cdr r)) cs)))
   :hints (("Goal" :use rt-read-atom-is-canonical
            :in-theory (enable rt-reader-object-text)))))

(local
 (defthm rt-tail-text-of-scanned-atom
   (let ((r (boymoo::lex-atom cs pkgs)))
     (implies (and r (car r) (consp (cdr r)) (equal (cadr r) #\)))
              (equal (rt-reader-tail-text (car r) (cddr r))
                     (list* #\Space #\. #\Space cs))))
   :hints (("Goal" :use rt-read-atom-is-canonical
            :in-theory (enable rt-reader-tail-text)))))

; At each successful return, restore the text using the values in the
; result. Any suffix beyond the line feed stays after the line.
(local
 (defthm rt-reader-tail-text-of-nil
   (equal (rt-reader-tail-text nil rest) (cons #\) rest))))

(local
 (defthm rt-open-frame-text-at-line-close
   (implies (not (consp (cdr stack)))
            (equal (rt-open-frames-text stack nil word rest)
                   (cons #\( (append word
                                     (rt-reader-arguments-text
                                      (cdr (revappend (car stack) nil)) rest)))))
   :hints (("Goal" :expand ((rt-open-frames-text stack nil word rest))))))

(local
 (defthm rt-parse-loop-restores-text
   (let ((r (boymoo::parse-loop cs stack elem pkgs)))
     (implies (and (booleanp elem) (rt-open-frames-p stack elem) r)
              (equal (rt-open-frames-text stack elem word cs)
                     (cons #\( (append word
                                       (rt-reader-arguments-text
                                        (cdar r) (list* #\) #\Newline (cdr r))))))))
   :hints (("Goal" :induct (boymoo::parse-loop cs stack elem pkgs)
            :expand ((:free (elem) (boymoo::parse-loop cs stack elem pkgs)))
            :in-theory (disable (:definition boymoo::parse-loop) rt-open-frames-text
                                rt-reader-tail-text rt-reader-object-text
                                rt-reader-arguments-text)
            :do-not '(generalize fertilize) :do-not-induct t))
   :rule-classes nil))

; The tag can be shared by two words in an arbitrary word table.
; Recover the spelling from the input before the parser replaces it.
(defun rt-line-word (cs)
  (coerce (revappend (car (boymoo::lex-word (cdr cs) nil)) nil) 'string))

(local
 (defthm rt-word-scan-keeps-text
   (let ((r (boymoo::lex-word cs acc)))
     (and (equal (revappend (car r) (cdr r)) (revappend acc cs))
          (implies (character-listp acc) (character-listp (car r)))))
   :hints (("Goal" :induct (boymoo::lex-word cs acc)))))

(defthm rt-accepted-line-has-reader-text
  (implies (boymoo::parse-line cs words pkgs)
           (equal cs (rt-reader-line-text
                      (rt-line-word cs)
                      (cdr (boymoo::parse-line cs words pkgs)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rt-word-scan-keeps-text (cs (cdr cs)) (acc nil))
                 (:instance rt-parse-loop-restores-text
                            (cs (cdr (boymoo::lex-word (cdr cs) nil)))
                            (stack (list (list (cdr
                                      (boymoo::pair-of
                                       (revappend (car (boymoo::lex-word (cdr cs) nil)) nil)
                                       words)))))
                            (elem nil)
                            (word (revappend (car (boymoo::lex-word (cdr cs) nil)) nil))))
           :in-theory (e/d (rt-open-frames-text)
                            (boymoo::parse-loop boymoo::lex-word boymoo::pair-of
                             rt-word-scan-keeps-text rt-reader-arguments-text))
           :do-not-induct t)))

; The word scan consumes format characters. A word table with no empty
; key ensures that a successful scan names a nonempty word.
(local
 (defthm rt-word-scan-records-word-characters
   (implies (rt-word-chars-p acc)
            (rt-word-chars-p (car (boymoo::lex-word cs acc))))
   :hints (("Goal" :induct (boymoo::lex-word cs acc)))))

(local
 (defthm rt-reversing-word-characters
   (implies (rt-word-chars-p cs)
            (equal (rt-word-chars-p (revappend cs acc)) (rt-word-chars-p acc)))
   :hints (("Goal" :induct (revappend cs acc)))))

(local
 (defthm rt-word-characters-are-characters
   (implies (rt-word-chars-p cs) (character-listp cs))))

(defthm rt-accepted-line-has-format-word
  (implies (and (boymoo::parse-line cs words pkgs)
                (not (boymoo::pair-of nil words)))
           (rt-word-p (rt-line-word cs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable boymoo::lex-word boymoo::parse-loop
                                     boymoo::pair-of))))

; A datum from the reader contains format atoms and admitted symbols.
; A NIL that ends a list is implicit and requires no package lookup.
(defun rt-reader-datum-in-table-p (x pkgs)
  (if (consp x)
      (and (rt-reader-datum-in-table-p (car x) pkgs)
           (or (null (cdr x)) (rt-reader-datum-in-table-p (cdr x) pkgs)))
    (rt-reader-atom-in-table-p x pkgs)))

(defun rt-reader-list-in-table-p (xs pkgs)
  (and (true-listp xs)
       (or (null xs) (rt-reader-datum-in-table-p xs pkgs))))

(local
 (defthm rt-reader-datum-of-scanned-atom
   (let ((r (boymoo::lex-atom cs pkgs)))
     (implies r
              (rt-reader-datum-in-table-p (car r) pkgs)))
   :hints (("Goal" :use rt-read-atom-is-canonical))))

(local
 (defthm rt-push-onto-reader-list
   (equal (rt-reader-list-in-table-p (cons x xs) pkgs)
          (and (rt-reader-datum-in-table-p x pkgs)
               (rt-reader-list-in-table-p xs pkgs)))))

(local
 (defthm rt-empty-arguments-are-in-table
   (rt-reader-list-in-table-p nil pkgs)))

(local
 (defthm rt-reader-list-of-append
   (implies (true-listp xs)
            (equal (rt-reader-list-in-table-p (append xs ys) pkgs)
                   (and (rt-reader-list-in-table-p xs pkgs)
                        (rt-reader-list-in-table-p ys pkgs))))
   :hints (("Goal" :induct (append xs ys)
            :in-theory (disable rt-reader-list-in-table-p
                                rt-reader-datum-in-table-p)))))

(local
 (defthm rt-reader-data-of-reversed-frame
   (implies (and (rt-reader-list-in-table-p xs pkgs)
                 (or (null tail) (rt-reader-datum-in-table-p tail pkgs)))
            (or (null (revappend xs tail))
                (rt-reader-datum-in-table-p (revappend xs tail) pkgs)))
   :hints (("Goal" :induct (revappend xs tail)
            :in-theory (disable rt-reader-list-in-table-p)))))

(local
 (defthm rt-reader-datum-of-nonempty-reversed-frame
   (implies (and (consp xs) (rt-reader-list-in-table-p xs pkgs)
                 (or (null tail) (rt-reader-datum-in-table-p tail pkgs)))
            (rt-reader-datum-in-table-p (revappend xs tail) pkgs))
   :hints (("Goal" :use (rt-reader-data-of-reversed-frame
                         (:instance rt-consp-of-revappend (x xs) (y tail)))
            :in-theory (disable rt-consp-of-revappend
                                rt-reader-data-of-reversed-frame)))))

; Inner frames contain reversed data. The last element of the outer
; frame is the tag of the word, which is outside the datum domain.
(local
 (defun rt-frame-data-p (stack elem pkgs)
   (and (consp stack)
        (if (consp (cdr stack))
            (and (or elem (consp (car stack)))
                 (rt-reader-list-in-table-p (car stack) pkgs)
                 (rt-frame-data-p (cdr stack) t pkgs))
          (and (consp (car stack))
               (rt-reader-list-in-table-p (cdr (revappend (car stack) nil)) pkgs))))))

(local
 (defthm rt-data-frames-are-nonempty
   (implies (rt-frame-data-p stack elem pkgs) (consp stack))
   :rule-classes :forward-chaining))

(local
 (defthm rt-frame-data-opening-a-list
   (implies (rt-frame-data-p stack t pkgs)
            (rt-frame-data-p (cons nil stack) t pkgs))
   :hints (("Goal" :expand ((rt-frame-data-p (cons nil stack) t pkgs))))))

(local
 (defthm rt-frame-data-after-a-space
   (implies (rt-frame-data-p stack nil pkgs)
            (rt-frame-data-p stack t pkgs))
   :hints (("Goal" :expand ((rt-frame-data-p stack nil pkgs)
                            (rt-frame-data-p stack t pkgs))))))

(local
 (defthm rt-frame-data-after-an-element
   (implies (and (rt-frame-data-p stack t pkgs)
                 (rt-reader-datum-in-table-p x pkgs))
            (rt-frame-data-p (cons (cons x (car stack)) (cdr stack)) nil pkgs))
   :hints (("Goal" :expand ((rt-frame-data-p stack t pkgs)
                            (rt-frame-data-p (cons (cons x (car stack)) (cdr stack))
                                             nil pkgs))
            :in-theory (disable rt-reader-list-in-table-p
                                rt-reader-datum-in-table-p)))))

(local
 (defthm rt-frame-data-after-a-list
   (implies (and (rt-frame-data-p stack nil pkgs) (consp (cdr stack))
                 (or (null tail) (rt-reader-datum-in-table-p tail pkgs)))
            (rt-frame-data-p
             (cons (cons (revappend (car stack) tail) (cadr stack)) (cddr stack))
             nil pkgs))
   :hints (("Goal" :use ((:instance rt-frame-data-after-an-element
                                     (stack (cdr stack))
                                     (x (revappend (car stack) tail)))
                         (:instance rt-reader-datum-of-nonempty-reversed-frame (xs (car stack))))
            :expand ((rt-frame-data-p stack nil pkgs))
            :in-theory (disable rt-frame-data-after-an-element
                                rt-reader-datum-of-nonempty-reversed-frame
                                rt-reader-list-in-table-p
                                rt-reader-datum-in-table-p)))))

(local
 (defthm rt-outer-frame-has-arguments
   (implies (and (rt-frame-data-p stack elem pkgs) (not (consp (cdr stack))))
            (rt-reader-list-in-table-p (cdr (revappend (car stack) nil)) pkgs))
   :hints (("Goal" :expand ((rt-frame-data-p stack elem pkgs))))))

(local
 (defthm rt-parse-loop-reads-arguments-in-table
   (let ((r (boymoo::parse-loop cs stack elem pkgs)))
     (implies (and (booleanp elem) (rt-frame-data-p stack elem pkgs) r)
              (rt-reader-list-in-table-p (cdar r) pkgs)))
   :rule-classes nil
   :hints (("Goal" :induct (boymoo::parse-loop cs stack elem pkgs)
            :expand ((:free (elem) (boymoo::parse-loop cs stack elem pkgs)))
            :in-theory (disable (:definition boymoo::parse-loop)
                                rt-frame-data-p rt-reader-datum-in-table-p
                                rt-reader-list-in-table-p)
            :do-not '(generalize fertilize) :do-not-induct t))))

(defthm rt-accepted-arguments-are-in-table
  (let ((r (boymoo::parse-line cs words pkgs)))
    (implies r (rt-reader-list-in-table-p (cdr r) pkgs)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rt-parse-loop-reads-arguments-in-table
                            (cs (cdr (boymoo::lex-word (cdr cs) nil)))
                            (stack (list (list (cdr
                                      (boymoo::pair-of
                                       (revappend (car (boymoo::lex-word (cdr cs) nil)) nil)
                                       words)))))
                            (elem nil)))
           :in-theory (disable boymoo::lex-word boymoo::parse-loop
                               boymoo::pair-of)
           :do-not-induct t)))

; Rendering the reader's form of a native datum gives the same text.
(defthm rt-datum-form-of-cons
  (implies (consp x)
           (equal (rt-datum-form x)
                  (cons (rt-datum-form (car x)) (rt-datum-form (cdr x)))))
  :hints (("Goal" :expand ((rt-datum-form x)))))

(local
 (defthm rt-datum-form-keeps-cons-status
   (equal (consp (rt-datum-form x)) (consp x))
   :hints (("Goal" :expand ((rt-datum-form x))))))

(local
 (defthm rt-datum-form-keeps-nil-status
   (implies (rt-format-datum-p x)
            (iff (rt-datum-form x) x))
   :hints (("Goal" :use ((:instance rt-datum-form-injective (y nil)))
            :in-theory (disable rt-datum-form rt-datum-form-injective)))))

(local
 (defun rt-reader-text-induction (x rest)
   (if (consp x)
       (list (rt-reader-text-induction (cdr x) rest)
             (rt-reader-text-induction (car x) (rt-tail-text (cdr x) rest)))
     rest)))

(local
 (defthm rt-reader-text-of-datum-form
   (implies (rt-format-datum-p x)
            (and (equal (rt-reader-object-text (rt-datum-form x) rest)
                        (rt-object-text x rest))
                 (equal (rt-reader-tail-text (rt-datum-form x) rest)
                        (rt-tail-text x rest))))
   :hints (("Goal" :induct (rt-reader-text-induction x rest)
            :in-theory (disable rt-datum-form)
            :expand ((rt-object-text x rest) (rt-tail-text x rest)
                     (rt-reader-object-text (rt-datum-form x) rest)
                     (rt-reader-tail-text (rt-datum-form x) rest)
                     (rt-reader-object-text (cons (rt-datum-form (car x))
                                                  (rt-datum-form (cdr x))) rest)
                     (rt-reader-tail-text (cons (rt-datum-form (car x))
                                                (rt-datum-form (cdr x))) rest))))))

(local
 (defthm rt-reader-arguments-text-of-datum-form
   (implies (and (true-listp args) (rt-format-datum-p args))
            (equal (rt-reader-arguments-text (rt-datum-form args) rest)
                   (rt-arguments-text args rest)))
   :hints (("Goal" :induct (rt-arguments-text args rest)
            :in-theory (disable rt-reader-object-text rt-object-text
                                rt-reader-tail-text rt-tail-text)))))

(defthm rt-accepted-line-is-printer-text
  (implies (and (boymoo::parse-line cs words pkgs)
                (rt-word-p (rt-line-word cs))
                (true-listp args)
                (rt-format-datum-p args)
                (equal (cdr (boymoo::parse-line cs words pkgs))
                       (rt-datum-form args)))
           (equal cs (append (coerce (bm-line (rt-line-word cs) args) 'list)
                             '(#\Newline))))
  :rule-classes nil
  :hints (("Goal" :use (rt-accepted-line-has-reader-text
                       (:instance rt-bm-line-with-trailing-characters
                                  (word (rt-line-word cs)) (rest '(#\Newline))))
           :in-theory (disable boymoo::parse-line rt-line-word rt-word-p bm-line
                               rt-arguments-text rt-reader-arguments-text rt-datum-form))))
