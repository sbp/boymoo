(in-package "ACL2")

(include-book "structure-events")

; The world registers function, theorem and reserved names by properties.

(defun structure-registered-symbol-p (name wrld)
  (and (symbolp name)
       (or (not (eq (getpropc name 'formals t wrld) t))
           (getpropc name 'theorem nil wrld)
           (structure-reserved-name-p name wrld))))

(defthm structure-fresh-name-excludes-registered-symbols
  (let ((name (bx-fresh-name base i fn wrld fuel)))
    (implies name
             (and (symbolp name)
                  (not (keywordp name))
                  (not (structure-registered-symbol-p name wrld))
                  (equal (symbol-package-name name) (symbol-package-name fn)))))
  :hints (("Goal" :induct (bx-fresh-name base i fn wrld fuel)
                  :in-theory (disable fgetprop))))

; Read a formula name from the end.  One decimal group can mark a
; constraint position, and a second can distinguish an occupied name.
; For uniqueness across statements, only the originating symbol matters.

(defun structure-decimal-digit-p (char)
  (member-equal char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))

(defun structure-skip-digits (chars)
  (if (and (consp chars) (structure-decimal-digit-p (car chars)))
      (structure-skip-digits (cdr chars))
    chars))

(defun structure-drop-number (chars)
  (if (and (consp chars) (structure-decimal-digit-p (car chars)))
      (let ((tail (structure-skip-digits chars)))
        (if (eql (car tail) #\Space) (cdr tail) chars))
    chars))

(defun structure-tail-after-prefix (prefix chars)
  (cond ((endp prefix) (list chars))
        ((and (consp chars) (eql (car prefix) (car chars)))
         (structure-tail-after-prefix (cdr prefix) (cdr chars)))
        (t nil)))

(defun structure-name-stem (reversed-spelling)
  (let ((tail (structure-drop-number (structure-drop-number reversed-spelling))))
    (or (structure-tail-after-prefix (revappend (coerce " definition" 'list) nil) tail)
        (structure-tail-after-prefix (revappend (coerce " choice" 'list) nil) tail)
        (structure-tail-after-prefix (revappend (coerce " constraint" 'list) nil) tail))))

(defun structure-symbol-spelling (symbol)
  (cons (symbol-package-name symbol)
        (revappend (coerce (symbol-name symbol) 'list) nil)))

(defun structure-name-source (name)
  (and (symbolp name)
       (let ((stem (structure-name-stem (revappend (coerce (symbol-name name) 'list) nil))))
         (and stem (cons (symbol-package-name name) (car stem))))))

; The decimal part of a generated name contains digits and no spaces.

(local (include-book "arithmetic/idiv" :dir :system))

(defun structure-decimal-charsp (chars)
  (if (endp chars)
      (null chars)
    (and (structure-decimal-digit-p (car chars))
         (structure-decimal-charsp (cdr chars)))))

(local (defthm structure-digit-to-char-in-decimal
         (implies (and (natp n) (< n 10))
                  (structure-decimal-digit-p (digit-to-char n)))
         :hints (("Goal" :in-theory (enable digit-to-char)))))

(local (defthm structure-positive-mod-is-rem
         (implies (natp n)
                  (equal (mod n 10) (rem n 10)))
         :hints (("Goal" :in-theory (enable mod rem floor truncate)))))

(local (defthm structure-remainder-of-integer-is-integer
         (implies (integerp n) (integerp (rem n 10)))
         :hints (("Goal" :in-theory (enable rem truncate)))))

(local (defthm structure-decimal-digit-of-remainder
         (implies (natp n)
                  (structure-decimal-digit-p (digit-to-char (mod n 10))))
         :hints (("Goal"
                  :use ((:instance structure-digit-to-char-in-decimal (n (rem n 10)))
                        (:instance rem-lower-bound (x n) (y 10))
                        (:instance rem-upper-bound (x n) (y 10)))
                  :in-theory (disable structure-decimal-digit-p digit-to-char mod rem
                                      structure-digit-to-char-in-decimal)))))

(local (defthm structure-decimal-charsp-of-explode
         (implies (structure-decimal-charsp acc)
                  (structure-decimal-charsp (explode-nonnegative-integer n 10 acc)))
         :hints (("Goal" :induct (explode-nonnegative-integer n 10 acc)
                         :in-theory (disable digit-to-char mod floor
                                             structure-decimal-digit-p
                                             structure-positive-mod-is-rem)))))

(local (defthm structure-decimal-characters-form-a-list
         (implies (structure-decimal-charsp chars)
                  (character-listp chars))))

(local (defthm structure-revappend-decimal-characters
         (implies (and (structure-decimal-charsp chars)
                       (structure-decimal-charsp acc))
                  (structure-decimal-charsp (revappend chars acc)))
         :hints (("Goal" :induct (revappend chars acc)
                         :in-theory (disable structure-decimal-digit-p)))))

(local (defthm structure-explode-decimal-is-nonempty
         (consp (explode-nonnegative-integer n 10 nil))
         :hints (("Goal" :induct (explode-nonnegative-integer n 10 nil)))))

(local (defthm structure-reversed-decimal-is-nonempty
         (implies (consp chars)
                  (consp (revappend chars nil)))))

(local (defthm structure-skip-decimal-prefix
         (implies (and (structure-decimal-charsp digits)
                       (not (structure-decimal-digit-p (car tail))))
                  (equal (structure-skip-digits (append digits tail)) tail))
         :hints (("Goal" :induct (append digits tail)
                         :in-theory (disable structure-decimal-digit-p)))))

(local (defthm structure-drop-decimal-prefix
         (implies (and (structure-decimal-charsp digits) (consp digits))
                  (equal (structure-drop-number (append digits (cons #\Space tail)))
                         tail))
         :hints (("Goal" :in-theory (disable structure-decimal-digit-p
                                             structure-skip-digits)))))

(local (defthm structure-letter-precedes-no-number
         (implies (not (structure-decimal-digit-p char))
                  (equal (structure-drop-number (cons char tail)) (cons char tail)))))

(local (defthm structure-characters-of-string-append
         (equal (coerce (string-append a b) 'list)
                (append (coerce a 'list) (coerce b 'list)))
         :hints (("Goal" :in-theory (enable string-append)))))

(local (defthm structure-reversed-append
         (equal (revappend (append a b) acc)
                (revappend b (revappend a acc)))))

(local (defthm structure-append-to-revappend
         (equal (append (revappend a b) c)
                (revappend a (append b c)))
         :hints (("Goal" :induct (revappend a b)))))

(local (defthm structure-reverse-into-append
         (equal (revappend a b)
                (append (revappend a nil) b))
         :rule-classes nil))

(local (defthm structure-drop-number-in-reversed-text
         (implies (natp i)
                  (equal (structure-drop-number
                          (revappend (explode-nonnegative-integer i 10 nil)
                                     (cons #\Space rest)))
                         rest))
         :hints (("Goal"
                  :use ((:instance structure-reverse-into-append
                                   (a (explode-nonnegative-integer i 10 nil))
                                   (b (cons #\Space rest))))
                  :in-theory (disable structure-drop-number
                                      explode-nonnegative-integer revappend
                                      structure-append-to-revappend)))))

(defun structure-position-word (position)
  (concatenate 'string "constraint "
               (coerce (explode-nonnegative-integer position 10 nil) 'string)))

(local (in-theory (disable explode-nonnegative-integer)))

; Reading from the right recovers the whole stem even if it contains
; spaces, digits or a word also used as a suffix.

(local (defthm structure-definition-stem
         (equal (structure-name-stem
                 (revappend (coerce (concatenate 'string stem " definition") 'list) nil))
                (list (revappend (coerce stem 'list) nil)))
         :hints (("Goal" :in-theory (disable string-append)))))

(local (defthm structure-choice-stem
         (equal (structure-name-stem
                 (revappend (coerce (concatenate 'string stem " choice") 'list) nil))
                (list (revappend (coerce stem 'list) nil)))
         :hints (("Goal" :in-theory (disable string-append)))))

(local (defthm structure-position-stem
         (implies (natp position)
                  (equal (structure-name-stem
                          (revappend (coerce (concatenate 'string stem " "
                                                          (structure-position-word position))
                                             'list)
                                     nil))
                         (list (revappend (coerce stem 'list) nil))))
         :hints (("Goal" :in-theory (disable string-append structure-drop-number)))))

(local (defthm structure-candidate-spelling-stem
         (implies (and (natp i)
                       (natp position)
                       (member-equal word
                                     (list "definition" "choice"
                                           (structure-position-word position))))
                  (let* ((base (concatenate 'string stem " " word))
                         (spelling
                          (if (equal i 0)
                              base
                            (concatenate 'string base " "
                                         (coerce (explode-nonnegative-integer i 10 nil)
                                                 'string)))))
                    (equal (structure-name-stem (revappend (coerce spelling 'list) nil))
                           (list (revappend (coerce stem 'list) nil)))))
         :hints (("Goal"
                  :in-theory (disable string-append structure-drop-number)))))

(local (defthm structure-fresh-name-spelling-source
         (implies (and (symbolp owner)
                       (natp i)
                       (natp position)
                       (member-equal word
                                     (list "definition" "choice"
                                           (structure-position-word position)))
                       (equal base (concatenate 'string (symbol-name owner) " " word))
                       (bx-fresh-name base i owner wrld fuel))
                  (equal (structure-name-source (bx-fresh-name base i owner wrld fuel))
                         (structure-symbol-spelling owner)))
         :hints (("Goal" :induct (bx-fresh-name base i owner wrld fuel)
                         :in-theory (disable string-append fgetprop
                                             structure-name-stem structure-position-word
                                             bx-in-use-p keywordp))
                 ("Subgoal *1/1"
                  :use ((:instance structure-candidate-spelling-stem
                                   (stem (symbol-name owner))))
                  :in-theory (disable structure-candidate-spelling-stem
                                      string-append fgetprop
                                      structure-name-stem structure-position-word
                                      bx-in-use-p keywordp)))))

(defthm structure-bx-formula-name-has-source
  (implies (and (symbolp owner)
                (natp position)
                (member-equal word (list "definition" "choice" (structure-position-word position)))
                (bx-formula-name owner word wrld))
           (equal (structure-name-source (bx-formula-name owner word wrld))
                  (structure-symbol-spelling owner)))
  :hints (("Goal" :use ((:instance structure-fresh-name-spelling-source
                                   (base (concatenate 'string (symbol-name owner) " " word))
                                   (i 0) (fuel *bx-name-tries*)))
                  :in-theory (disable bx-fresh-name structure-name-source structure-symbol-spelling
                                      string-append revappend structure-position-word))))

(defthm structure-definition-name-source
  (implies (and (symbolp owner) (bx-formula-name owner "definition" wrld))
           (equal (structure-name-source (bx-formula-name owner "definition" wrld))
                  (structure-symbol-spelling owner)))
  :hints (("Goal" :use ((:instance structure-bx-formula-name-has-source
                                   (word "definition") (position 0)))
                  :in-theory (disable bx-formula-name structure-bx-formula-name-has-source
                                      structure-name-source structure-symbol-spelling)))
  :rule-classes nil)

(defthm structure-choice-name-source
  (implies (and (symbolp owner) (bx-formula-name owner "choice" wrld))
           (equal (structure-name-source (bx-formula-name owner "choice" wrld))
                  (structure-symbol-spelling owner)))
  :hints (("Goal" :use ((:instance structure-bx-formula-name-has-source
                                   (word "choice") (position 0)))
                  :in-theory (disable bx-formula-name structure-bx-formula-name-has-source
                                      structure-name-source structure-symbol-spelling)))
  :rule-classes nil)

(defthm structure-position-name-source
  (implies (and (symbolp owner) (natp position)
                (bx-formula-name owner (structure-position-word position) wrld))
           (equal (structure-name-source (bx-formula-name owner (structure-position-word position)
                                                         wrld))
                  (structure-symbol-spelling owner)))
  :hints (("Goal" :use ((:instance structure-bx-formula-name-has-source
                                   (word (structure-position-word position))))
                  :in-theory (disable bx-formula-name structure-bx-formula-name-has-source
                                      structure-name-source structure-symbol-spelling
                                      structure-position-word)))
  :rule-classes nil)
