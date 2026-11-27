(in-package "BOYMOO-PROOFS")

(include-book "program-elaboration")

(logic)
(set-verify-guards-eagerness 0)

; The spelling check validates the bytes used to make each candidate.
(defun data-hex-digit-candidate (byte)
  (let ((code (char-code byte)))
    (cond ((and (<= 48 code) (<= code 57)) (- code 48))
          ((and (<= 65 code) (<= code 70)) (- code 55))
          (t 0))))

(defun data-hex-byte-candidate (text position)
  (code-char (+ (* 16 (data-hex-digit-candidate (char text position)))
                (data-hex-digit-candidate (char text (1+ position))))))

(defun data-string-byte-candidates (text position left)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      nil
    (let ((byte (char text position)))
      (if (equal byte #\\)
          (if (< left 3)
              nil
            (cons (data-hex-byte-candidate text (1+ position))
                  (data-string-byte-candidates text (+ position 3) (- left 3))))
        (cons byte (data-string-byte-candidates text (1+ position) (1- left)))))))

(defun data-atom-value-candidate (text packages)
  (if (or (not (stringp text)) (equal (length text) 0))
      nil
    (let ((first (char text 0)) (size (length text)))
      (cond ((equal first #\") (coerce (data-string-byte-candidates text 1 (- size 2)) 'string))
            ((equal first #\#)
             (cond ((and (equal size 4) (equal (char text 1) #\\)) (data-hex-byte-candidate text 2))
                   ((data-complex-text-p text)
                    (let* ((end (1- size)) (space (boymoo-compiler::find-char text 3 (- end 3) #\Space)))
                      (complex (data-rational-text-value (subseq text 3 space))
                               (data-rational-text-value (subseq text (1+ space) end)))))
                   (t nil)))
            ((boymoo-compiler::symbol-separator text)
             (mv-let (ok symbol) (data-elaborate-symbol text packages)
               (and ok symbol)))
            (t (data-rational-text-value text))))))

(defun data-datum-value-candidate (kind parsed packages)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :datum) 1 0))))
  (if (eq kind :datum)
      (if (consp parsed) (data-datum-value-candidate :items parsed packages)
        (data-atom-value-candidate parsed packages))
    (cond ((atom parsed) nil)
          ((equal (car parsed) ".") (data-atom-value-candidate (cadr parsed) packages))
          (t (cons (data-datum-value-candidate :datum (car parsed) packages)
                   (data-datum-value-candidate :items (cdr parsed) packages))))))

(defun data-elaborate-quote (text packages)
  (if (and (stringp text) (posp (length text)))
      (if (equal (char text 0) #\()
          (let ((size (length text)))
            (mv-let (ok events forms) (data-infer-reader-events text 0 size nil nil nil size)
              (let* ((parsed (car forms)) (value (data-datum-value-candidate :datum parsed packages)))
                (mv (and ok (consp forms) (null (cdr forms)) (consp value)
                         (data-constant-spells-value-p text events parsed value))
                    value (list events parsed)))))
        (let ((value (data-atom-value-candidate text packages)))
          (mv (data-constant-spells-value-p text nil nil value) value '(nil nil))))
    (mv nil nil nil)))

(local
 (in-theory (disable data-atom-value-candidate data-datum-value-candidate data-infer-reader-events
                     data-constant-spells-value-p char length)))

(defthmd data-elaborated-quote-supplies-its-spelling
  (mv-let (ok value witness) (data-elaborate-quote text packages)
    (implies ok (data-constant-spells-value-p text (car witness) (cadr witness) value))))

(local (in-theory (disable data-elaborate-quote)))

(defun data-elaborate-quote-list (texts packages)
  (if (atom texts)
      (mv (null texts) nil nil)
    (mv-let (first-ok value witness) (data-elaborate-quote (car texts) packages)
      (mv-let (rest-ok bindings witnesses) (data-elaborate-quote-list (cdr texts) packages)
        (mv (and first-ok rest-ok) (cons (cons (car texts) value) bindings) (cons witness witnesses))))))

(defthmd data-elaborated-quote-list-supplies-checked-bindings
  (mv-let (ok bindings witnesses) (data-elaborate-quote-list texts packages)
    (implies ok (and (data-quote-spellings-p bindings witnesses) (equal (strip-cars bindings) texts))))
  :hints (("Goal" :induct (data-elaborate-quote-list texts packages)
                  :in-theory (enable data-elaborated-quote-supplies-its-spelling))))

(defun data-term-quoted-texts (kind parsed)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (cond ((atom parsed) nil)
            ((equal (car parsed) boymoo-compiler::*quote-name*) (list (cadr parsed)))
            ((consp (car parsed)) (append (data-term-quoted-texts :term (caddar parsed))
                                          (data-term-quoted-texts :terms (cdr parsed))))
            (t (data-term-quoted-texts :terms (cdr parsed))))
    (if (atom parsed)
        nil
      (append (data-term-quoted-texts :term (car parsed)) (data-term-quoted-texts :terms (cdr parsed))))))

(defun data-definition-quoted-texts (definitions)
  (if (atom definitions)
      nil
    (append (data-term-quoted-texts :term (caddar definitions)) (data-definition-quoted-texts (cdr definitions)))))

(defun data-program-quoted-texts (lines)
  (if (atom lines)
      nil
    (append (and (equal (caar lines) "define") (data-definition-quoted-texts (cddar lines)))
            (data-program-quoted-texts (cdr lines)))))

(local
 (defthm quote-membership-in-concatenated-texts
   (iff (member-equal text (append first rest))
        (or (member-equal text first) (member-equal text rest)))))

(local
 (defthm term-quoted-texts-cover-syntactic-occurrences
   (iff (member-equal text (data-term-quoted-texts kind parsed))
        (< 0 (data-term-quote-count kind parsed text)))
   :hints (("Goal" :induct (data-term-quoted-texts kind parsed)))))

(local
 (defthm definition-quoted-texts-cover-syntactic-occurrences
   (iff (member-equal text (data-definition-quoted-texts definitions))
        (< 0 (data-definition-quote-count definitions text)))
   :hints (("Goal" :induct (data-definition-quoted-texts definitions)
                   :in-theory (disable data-term-quoted-texts data-term-quote-count)))))

(defthmd data-program-quoted-texts-cover-all-syntactic-occurrences
  (iff (member-equal text (data-program-quoted-texts lines)) (< 0 (data-program-quote-count lines text)))
  :hints (("Goal" :induct (data-program-quoted-texts lines)
                  :in-theory (disable data-definition-quoted-texts data-definition-quote-count))))

(defun data-elaborate-program-with-quotes (text packages)
  (mv-let (read-ok events lines) (data-infer-program-spans text)
    (if (not read-ok)
        (mv nil nil nil nil nil nil)
      (mv-let (quotes-ok bindings witnesses) (data-elaborate-quote-list (data-program-quoted-texts lines) packages)
        (if (not quotes-ok)
            (mv nil nil nil nil nil nil)
          (mv-let (ok sources) (data-elaborate-program-lines lines packages bindings nil nil)
            (mv ok events lines sources bindings witnesses)))))))

(local
 (in-theory (disable data-elaborate-quote-list data-program-quoted-texts data-infer-program-spans
                     data-elaborate-program-lines data-program-spans-p data-source-lines-spelled-p
                     data-lookup-heads-spelled-p data-quote-spellings-p)))

(defthmd data-elaborated-program-with-quotes-supplies-all-checked-relations
  (mv-let (ok events lines sources bindings witnesses) (data-elaborate-program-with-quotes text packages)
    (implies ok (and (data-program-spans-p text events lines)
                     (data-source-lines-spelled-p lines sources bindings nil nil)
                     (data-lookup-heads-spelled-p lines sources)
                     (data-quote-spellings-p bindings witnesses)
                     (equal (strip-cars bindings) (data-program-quoted-texts lines)))))
  :hints (("Goal" :use (data-inferred-program-spans-validate
                        (:instance data-elaborated-quote-list-supplies-checked-bindings
                                   (texts (data-program-quoted-texts (mv-nth 2 (data-infer-program-spans text)))))
                        (:instance data-elaborated-program-lines-agree-with-text-and-lookup-heads
                                   (lines (mv-nth 2 (data-infer-program-spans text))) (entry nil) (target nil)
                                   (bindings (mv-nth 1 (data-elaborate-quote-list
                                                        (data-program-quoted-texts
                                                         (mv-nth 2 (data-infer-program-spans text))) packages))))))))
