(in-package "ACL2")

(include-book "faithful-constraint-names")
(local (include-book "std/strings/explode-nonnegative-integer" :dir :system))
(local (include-book "std/lists/rev" :dir :system))

; A generated label identifies an anchor symbol. The last components
; are a purpose word, a position for a constraint conjunct, and an
; optional decimal suffix. Decode them from right to left so that
; spaces in the anchor's own name are preserved.

(defund faithful-label-purpose (kind position)
  (case kind
    (:definition "definition")
    (:choice "choice")
    (otherwise (faithful-conjunct-label-purpose position))))

(defun faithful-chars-after-name-component (chars)
  (cond ((endp chars) nil)
        ((eql (car chars) #\Space) (cdr chars))
        (t (faithful-chars-after-name-component (cdr chars)))))

(defund faithful-decimal-character-p (char)
  (and (characterp char)
       (<= (char-code #\0) (char-code char))
       (<= (char-code char) (char-code #\9))))

(defund faithful-drop-decimal-component (chars)
  (if (faithful-decimal-character-p (car chars))
      (faithful-chars-after-name-component chars)
    chars))

(defund faithful-reversed-label-anchor (label)
  (faithful-chars-after-name-component
   (faithful-drop-decimal-component
    (faithful-drop-decimal-component
     (revappend (coerce (symbol-name label) 'list) nil)))))

(defund faithful-label-anchor (label)
  (intern-in-package-of-symbol
   (coerce (revappend (faithful-reversed-label-anchor label) nil) 'string)
   label))

(defund faithful-symbol-last-character (name)
  (car (revappend (coerce (symbol-name name) 'list) nil)))

(defun faithful-name-component-chars (chars)
  (if (or (endp chars) (eql (car chars) #\Space))
      nil
    (cons (car chars) (faithful-name-component-chars (cdr chars)))))

(defun faithful-value-of-reversed-decimal (digits)
  (if (endp digits)
      0
    (+ (- (char-code (car digits)) (char-code #\0))
       (* 10 (faithful-value-of-reversed-decimal (cdr digits))))))

; The final letter of the purpose word identifies its kind. If there
; are two decimal components, the one farther right is the suffix.

(defund faithful-label-key (label)
  (let* ((chars (revappend (coerce (symbol-name label) 'list) nil))
         (after-first (faithful-drop-decimal-component chars))
         (after-second (faithful-drop-decimal-component after-first)))
    (case (car after-second)
      (#\n (list :definition 0))
      (#\e (list :choice 0))
      (otherwise
       (list :constraint
             (faithful-value-of-reversed-decimal
              (faithful-name-component-chars
               (if (faithful-decimal-character-p (car after-first))
                   after-first
                 chars))))))))

(defund faithful-expected-label-key (kind position)
  (case kind
    (:definition (list :definition 0))
    (:choice (list :choice 0))
    (otherwise (list :constraint position))))

; Decimal components are nonempty and contain no space.

(local
 (defthm faithful-decimal-character-agrees
   (equal (faithful-decimal-character-p char) (str::dec-digit-char-p char))
   :hints (("Goal" :in-theory (enable faithful-decimal-character-p str::dec-digit-char-p
                                     char-fix)))))

(local
 (defthm faithful-decimal-spelling-is-nonempty
   (implies (or (consp acc) (null acc))
            (consp (explode-nonnegative-integer n base acc)))
   :hints (("Goal" :induct (explode-nonnegative-integer n base acc)
            :in-theory (enable explode-nonnegative-integer)))
   :rule-classes :type-prescription))

(local
 (defthm faithful-digits-have-no-space
   (implies (str::dec-digit-char-list*p chars)
            (not (member-equal #\Space chars)))
   :hints (("Goal" :induct (len chars)))))

(local
 (defthm faithful-after-a-space-delimited-component
   (implies (not (member-equal #\Space prefix))
            (equal (faithful-chars-after-name-component
                    (append prefix (cons #\Space tail)))
                   tail))
   :hints (("Goal" :induct (len prefix)))))

(local
 (defthm faithful-chars-of-a-space-delimited-component
   (implies (and (true-listp prefix) (not (member-equal #\Space prefix)))
            (equal (faithful-name-component-chars
                    (append prefix (cons #\Space tail)))
                   prefix))
   :hints (("Goal" :induct (len prefix)))))

(local
 (defthm faithful-decimal-component-is-dropped
   (equal (faithful-drop-decimal-component
           (append (rev (explode-nonnegative-integer n 10 nil))
                   (cons #\Space tail)))
          tail)
   :hints (("Goal"
            :in-theory (e/d (faithful-drop-decimal-component)
                            (explode-nonnegative-integer rev))))))

(local
 (defthm faithful-nondecimal-component-is-kept
   (implies (not (str::dec-digit-char-p (car chars)))
            (equal (faithful-drop-decimal-component chars) chars))
   :hints (("Goal" :in-theory (enable faithful-drop-decimal-component)))))

(local
 (defthm faithful-decimal-component-does-not-start-with-uppercase-e
   (implies (str::dec-digit-char-list*p chars)
            (not (equal (car chars) #\E)))
   :hints (("Goal" :cases ((consp chars))))))

(local
 (defthm faithful-reversed-decimal-value-agrees
   (implies (str::dec-digit-char-list*p digits)
            (equal (faithful-value-of-reversed-decimal digits)
                   (basic-unexplode-core digits)))
   :hints (("Goal" :induct (len digits)
            :in-theory (enable basic-unexplode-core str::dec-digit-char-value
                               str::dec-digit-char-p)))))

(local
 (defthm faithful-reversed-decimal-value-of-explosion
   (implies (natp n)
            (equal (faithful-value-of-reversed-decimal (rev (explode-nonnegative-integer n 10 nil)))
                   n))
   :hints (("Goal"
            :use ((:instance unexplode-nonnegative-integer-of-explode-nonnegative-integer))
            :in-theory (e/d (unexplode-nonnegative-integer)
                            (rev explode-nonnegative-integer))))))

; A letter component denotes the purpose and immediately follows the
; anchor. In the reversed spelling its separating space follows it.

(local
 (defthm faithful-explode-of-string-append
   (equal (str::explode (string-append left right))
          (append (str::explode left) (str::explode right)))
   :hints (("Goal" :in-theory (enable string-append)))))

(local
 (defthm faithful-symbol-name-of-interned-label
   (implies (symbolp fn)
            (let* ((stem (faithful-label-stem fn (faithful-label-purpose kind position)))
                   (spelling
                    (if (equal index 0)
                        stem
                      (concatenate 'string stem " "
                                   (coerce (explode-nonnegative-integer index 10 nil) 'string))))
                   (label (intern-in-package-of-symbol spelling fn)))
              (and (equal (faithful-reversed-label-anchor label)
                          (rev (str::explode (symbol-name fn))))
                   (not (eql (faithful-symbol-last-character label) #\E))
                   (implies (natp position)
                            (equal (faithful-label-key label)
                                   (faithful-expected-label-key kind position))))))
   :hints (("Goal"
            :in-theory (e/d (faithful-reversed-label-anchor faithful-label-stem
                             faithful-label-purpose faithful-conjunct-label-purpose
                             faithful-symbol-last-character faithful-label-key
                             faithful-expected-label-key)
                            (explode-nonnegative-integer str::explode
                             faithful-value-of-reversed-decimal string-append rev))))))

(local
 (defthm faithful-variant-decodes-anchor
   (implies (and (symbolp fn)
                 (faithful-label-variant-p
                  label (faithful-label-stem fn (faithful-label-purpose kind position))
                  fn index remaining))
            (and (equal (faithful-reversed-label-anchor label)
                        (rev (str::explode (symbol-name fn))))
                 (not (eql (faithful-symbol-last-character label) #\E))
                 (implies (natp position)
                          (equal (faithful-label-key label)
                                 (faithful-expected-label-key kind position)))))
   :hints
   (("Goal"
     :induct (faithful-label-variant-p
              label (faithful-label-stem fn (faithful-label-purpose kind position))
              fn index remaining)
     :in-theory (disable faithful-symbol-name-of-interned-label
                         string-append str::explode explode-nonnegative-integer))
    ("Subgoal *1/2" :use faithful-symbol-name-of-interned-label)
    ("Subgoal *1/1" :use faithful-symbol-name-of-interned-label))
   :rule-classes nil))

(local
 (defthm faithful-label-spelling-identifies-anchor-name
   (implies (and (symbolp fn)
                 (faithful-formula-label-p label fn (faithful-label-purpose kind position)))
            (and (equal (faithful-reversed-label-anchor label)
                        (rev (str::explode (symbol-name fn))))
                 (not (eql (faithful-symbol-last-character label) #\E))
                 (implies (natp position)
                          (equal (faithful-label-key label)
                                 (faithful-expected-label-key kind position)))))
   :hints
   (("Goal"
     :use ((:instance faithful-variant-decodes-anchor (index 0) (remaining 1000)))
     :in-theory (e/d (faithful-formula-label-p) (faithful-label-variant-p))
     :do-not-induct t))
   :rule-classes nil))

; ACL2 identifies a symbol by its name and home package. A label is in
; its anchor's home package even when the spelling has other imports.

(local
 (defthm faithful-matching-label-package-has-symbol-anchor
   (implies (and (symbolp label)
                 (equal (symbol-package-name label) (symbol-package-name fn)))
            (symbolp fn))
   :hints (("Goal"
            :use ((:instance completion-of-symbol-package-name (x fn))
                  (:instance symbol-package-name-of-symbol-is-not-empty-string (x label)))))
   :rule-classes nil))

(defthmd faithful-generated-label-identifies-anchor
  (implies (and (symbolp label)
                (faithful-formula-label-p label fn (faithful-label-purpose kind position)))
           (and (equal (faithful-label-anchor label) fn)
                (not (eql (faithful-symbol-last-character label) #\E))
                (implies (natp position)
                         (equal (faithful-label-key label)
                                (faithful-expected-label-key kind position)))))
  :hints
  (("Goal"
    :use (faithful-matching-label-package-has-symbol-anchor
          faithful-label-spelling-identifies-anchor-name
          (:instance intern-in-package-of-symbol-symbol-name (x fn) (y label)))
    :in-theory (e/d (faithful-formula-label-p faithful-label-anchor)
                    (faithful-label-variant-p rev str::explode
                     intern-in-package-of-symbol-symbol-name))
    :do-not-induct t)))

; A package rule ends in an uppercase E. The purpose and any suffix
; of a generated formula label have a different last character.

(defthm faithful-last-character-of-package-rule
  (equal (faithful-symbol-last-character
          (intern-in-package-of-symbol (concatenate 'string name "-PACKAGE") 'acl2::x))
         #\E)
  :hints (("Goal"
           :in-theory (e/d (faithful-symbol-last-character) (string-append rev str::explode)))))
