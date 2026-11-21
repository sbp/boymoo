; The representation of a datum in the reader and the rule of existence
; for its symbols.

(in-package "ACL2")

(include-book "round-trip-text")

; The format joins two independently delimited parts with two colons.
; The reader represents that text by a symbol in BOYMOO, except for the
; two symbols used for truth and for the end of a list.
(defund rt-symbol-text (package name)
  (append (rt-part-text (coerce package 'list))
          (list* #\: #\: (rt-part-text (coerce name 'list)))))

(defund rt-reader-symbol (package name)
  (let ((text (rt-symbol-text package name)))
    (cond ((equal text (coerce "COMMON-LISP::NIL" 'list)) nil)
          ((equal text (coerce "COMMON-LISP::T" 'list)) t)
          (t (intern-in-package-of-symbol (coerce text 'string)
                                          'boymoo::boymoo)))))

(defun rt-datum-form (x)
  (cond ((consp x) (cons (rt-datum-form (car x)) (rt-datum-form (cdr x))))
        ((symbolp x) (rt-reader-symbol (symbol-package-name x) (symbol-name x)))
        (t x)))

; A datum is one of the atoms of spec/language.md, section 1, or a cons of
; two data. Its symbols have the nonempty package names of section 2.
(defun rt-format-datum-p (x)
  (cond ((consp x)
         (and (rt-format-datum-p (car x)) (rt-format-datum-p (cdr x))))
        ((symbolp x) (not (equal (symbol-package-name x) "")))
        (t (or (rationalp x) (complex-rationalp x) (characterp x) (stringp x)))))

; The reader requires a package record and a miss in its import index.
; Both hidden and visible records are looked up the same way.
(defund rt-symbol-passes-index-p (package name pkgs)
  (let ((record (boymoo::trie-get (coerce package 'list) pkgs)))
    (and record
         (not (boymoo::trie-get (coerce name 'list) (boymoo::prec-trie record))))))

(defun rt-written-symbols-pass-index-p (x pkgs)
  (cond ((consp x)
         (and (rt-written-symbols-pass-index-p (car x) pkgs)
              (or (null (cdr x)) (rt-written-symbols-pass-index-p (cdr x) pkgs))))
        ((symbolp x) (rt-symbol-passes-index-p (symbol-package-name x) (symbol-name x)
                                        pkgs))
        (t t)))

; Every part has at least one character. These bounds distinguish the
; full name of a represented symbol from the names "T" and "NIL".
(defthm rt-part-text-consp
  (consp (rt-part-text cs))
  :hints (("Goal" :in-theory (enable rt-part-text))))

(local
 (defthm rt-part-text-length
   (< 0 (len (rt-part-text cs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable rt-part-text)))))

(defthm rt-symbol-text-length
  (< 3 (len (rt-symbol-text package name)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable rt-symbol-text))))

(local
 (defthm rt-part-text-characters
   (implies (character-listp cs)
            (character-listp (rt-part-text cs)))
   :hints (("Goal" :in-theory (e/d (rt-part-text) (rt-escaped-text))))))

(local
 (defthm rt-part-text-true-listp
   (implies (character-listp cs) (true-listp (rt-part-text cs)))
   :hints (("Goal" :use rt-part-text-characters
            :in-theory (disable rt-part-text-characters)))))

(defthm rt-symbol-text-characters
  (implies (and (stringp package) (stringp name))
           (character-listp (rt-symbol-text package name)))
  :hints (("Goal" :in-theory (enable rt-symbol-text))))

; Reading two symbol parts recovers the two strings used to make them.
(local
 (defthm rt-lex-whole-part
   (implies (character-listp cs)
            (equal (boymoo::lex-part (rt-part-text cs))
                   (list cs (rt-part-text cs))))
   :hints (("Goal" :use ((:instance rt-lex-part-of-text (rest nil)))
            :in-theory (disable rt-lex-part-of-text)))))

(defund rt-symbol-text-components (text)
  (let* ((package (boymoo::lex-part text))
         (name (boymoo::lex-part (cddddr package))))
    (list (coerce (car package) 'string) (coerce (car name) 'string))))

(defthm rt-symbol-text-components-of-text
  (implies (and (stringp package) (stringp name))
           (equal (rt-symbol-text-components (rt-symbol-text package name))
                  (list package name)))
  :hints (("Goal" :in-theory (enable rt-symbol-text-components rt-symbol-text))))

(local
 (defthm rt-symbol-text-injective
   (implies (and (stringp package1) (stringp name1)
                 (stringp package2) (stringp name2)
                 (equal (rt-symbol-text package1 name1)
                        (rt-symbol-text package2 name2)))
            (and (equal package1 package2) (equal name1 name2)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance rt-symbol-text-components-of-text
                                     (package package1) (name name1))
                         (:instance rt-symbol-text-components-of-text
                                     (package package2) (name name2)))
            :in-theory (disable rt-symbol-text-components-of-text)))))

; Recover the symbol text from its representative. ACL2's interning
; axiom then identifies two native symbols with the same pair of names.
(local
 (defthm rt-rendered-symbol-length
   (implies (and (stringp package) (stringp name))
            (< 3 (length (coerce (rt-symbol-text package name) 'string))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable length)))))

(local
 (defthm rt-intern-of-symbol-text-is-ordinary
   (implies (and (stringp package) (stringp name))
            (let ((s (intern-in-package-of-symbol
                      (coerce (rt-symbol-text package name) 'string)
                      'boymoo::boymoo)))
              (and (not (equal s nil)) (not (equal s t)))))
   :hints (("Goal"
            :use ((:instance symbol-name-intern-in-package-of-symbol
                             (s (coerce (rt-symbol-text package name) 'string))
                             (any-symbol 'boymoo::boymoo))
                  rt-rendered-symbol-length)
            :in-theory (disable length symbol-name-intern-in-package-of-symbol)))))

(local
 (defthm rt-text-of-reader-symbol
   (implies (and (stringp package) (stringp name))
            (equal (boymoo::sym-text (rt-reader-symbol package name))
                   (rt-symbol-text package name)))
   :hints (("Goal" :use rt-intern-of-symbol-text-is-ordinary
            :in-theory (e/d (rt-reader-symbol) (rt-intern-of-symbol-text-is-ordinary))))))

(defthm rt-reader-symbol-injective
  (implies (and (stringp package1) (stringp name1)
                (stringp package2) (stringp name2)
                (equal (rt-reader-symbol package1 name1)
                       (rt-reader-symbol package2 name2)))
           (and (equal package1 package2) (equal name1 name2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rt-text-of-reader-symbol (package package1) (name name1))
                 (:instance rt-text-of-reader-symbol (package package2) (name name2))
                 rt-symbol-text-injective)
           :in-theory (disable rt-text-of-reader-symbol boymoo::sym-text))))

(local
 (defthm rt-native-symbol-injective
   (implies (and (symbolp x) (symbolp y))
            (equal (equal (rt-reader-symbol (symbol-package-name x) (symbol-name x))
                          (rt-reader-symbol (symbol-package-name y) (symbol-name y)))
                   (equal x y)))
   :hints (("Goal"
            :use ((:instance rt-reader-symbol-injective
                             (package1 (symbol-package-name x)) (name1 (symbol-name x))
                             (package2 (symbol-package-name y)) (name2 (symbol-name y)))
                  (:instance intern-in-package-of-symbol-symbol-name (x x) (y y))
                  (:instance intern-in-package-of-symbol-symbol-name (x y) (y y)))
            :in-theory (disable intern-in-package-of-symbol-symbol-name)))))

(defthm rt-reader-symbol-is-symbol
  (symbolp (rt-reader-symbol package name))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rt-reader-symbol))))

(defthm rt-datum-form-of-nil
  (equal (rt-datum-form nil) nil)
  :hints (("Goal" :in-theory (enable rt-reader-symbol rt-symbol-text rt-part-text))))

(local
 (defun rt-datum-pair-induction (x y)
   (if (and (consp x) (consp y))
       (list (rt-datum-pair-induction (car x) (car y))
             (rt-datum-pair-induction (cdr x) (cdr y)))
     nil)))

(defthm rt-datum-form-injective
  (implies (and (rt-format-datum-p x) (rt-format-datum-p y))
           (equal (equal (rt-datum-form x) (rt-datum-form y))
                  (equal x y)))
  :hints (("Goal" :induct (rt-datum-pair-induction x y)
           :expand ((rt-datum-form x) (rt-datum-form y)))))

; A printed symbol is read by scanning its package, its two colons,
; and its name, then checking the package declaration and import index.
(defthm rt-print-symbol
  (implies (symbolp x)
           (equal (bm-obj x acc)
                  (revappend (rt-symbol-text (symbol-package-name x) (symbol-name x))
                             acc)))
  :hints (("Goal" :in-theory (enable rt-symbol-text)
           :expand ((bm-obj x acc)))))

(local
 (defthm rt-lex-symbol-text-after-package
   (implies (and (stringp package) (stringp name)
                 (not (rt-plain-char-p (car rest)))
                 (rt-symbol-passes-index-p package name pkgs))
            (equal (boymoo::lex-symbol-rest
                    (list* (coerce package 'list)
                           (rt-part-text (coerce package 'list))
                           #\: #\:
                           (append (rt-part-text (coerce name 'list)) rest))
                    pkgs)
                   (cons (rt-reader-symbol package name) rest)))
   :hints (("Goal" :in-theory (enable rt-symbol-passes-index-p rt-reader-symbol
                                     rt-symbol-text)))))

(local
 (defthm rt-part-text-first-when-quoted
   (implies (not (and (consp cs) (rt-all-plain-p cs)))
            (equal (car (rt-part-text cs)) #\|))
   :hints (("Goal" :in-theory (enable rt-part-text)))))

(local
 (defthm rt-part-text-when-plain
   (implies (and (consp cs) (rt-all-plain-p cs))
            (equal (rt-part-text cs) cs))
   :hints (("Goal" :in-theory (enable rt-part-text)))))

(local
 (defthm rt-lex-part-of-empty-bars
   (equal (boymoo::lex-part (list* #\| #\| rest))
          (list* nil '(#\| #\|) rest))
   :hints (("Goal" :in-theory (enable boymoo::lex-part boymoo::lex-quoted)))))

(local
 (defthm rt-lex-atom-of-package-part
   (implies (character-listp cs)
            (equal (boymoo::lex-atom
                    (append (rt-part-text cs) (cons #\: rest)) pkgs)
                   (boymoo::lex-symbol-rest
                    (list* cs (rt-part-text cs) #\: rest) pkgs)))
   :hints (("Goal" :cases ((and (consp cs) (rt-all-plain-p cs)))
            :in-theory (disable boymoo::lex-symbol-rest boymoo::lex-sharp
                                boymoo::number-value rt-all-plain-p rt-plain-char-p)
            :do-not-induct t))))

(defthm rt-lex-atom-of-symbol-text
  (implies (and (stringp package) (stringp name)
                (not (rt-plain-char-p (car rest)))
                (rt-symbol-passes-index-p package name pkgs))
           (equal (boymoo::lex-atom (append (rt-symbol-text package name) rest) pkgs)
                  (cons (rt-reader-symbol package name) rest)))
  :hints (("Goal" :in-theory (e/d (rt-symbol-text)
                                   (boymoo::lex-atom boymoo::lex-symbol-rest)))))
