(in-package "BOYMOO-PROOFS")

(include-book "reader-spans")
(include-book "symbol-spelling")
(include-book "numbers")
(include-book "constant-retention")

(logic)
(set-verify-guards-eagerness 0)

(defun data-atom-spells-value-p (text value)
  (and (stringp text)
       (cond ((symbolp value)
              (let ((split (boymoo-compiler::symbol-separator text)))
                (data-symbol-spelling-p text split (symbol-package-name value) (symbol-name value))))
             ((stringp value)
              (and (equal (char text 0) #\")
                   (data-delimited-text-p text 0 (length text) (coerce value 'list))))
             ((characterp value) (data-character-text-p text value))
             ((rationalp value)
              (and (not (member-equal (char text 0) '(#\( #\" #\#)))
                   (not (boymoo-compiler::symbol-separator text))
                   (data-rational-text-p text) (equal (data-rational-text-value text) value)))
             ((complex-rationalp value)
              (let* ((end (1- (length text)))
                     (space (boymoo-compiler::find-char text 3 (- end 3) #\Space)))
                (and (data-complex-text-p text)
                     (equal (data-rational-text-value (subseq text 3 space)) (realpart value))
                     (equal (data-rational-text-value (subseq text (1+ space) end)) (imagpart value)))))
             (t nil))))

(local
 (in-theory (disable char length subseq boymoo-compiler::find-char boymoo-compiler::symbol-separator
                     boymoo-compiler::decode-part boymoo-compiler::decode-symbol-part
                     data-rational-text-p data-rational-text-value data-delimited-text-p)))

(local
 (defthm canonical-symbol-spelling-starts-with-a-symbol-byte
   (implies (data-symbol-spelling-p text split package name)
            (not (member-equal (char text 0) '(#\( #\" #\#))))
   :hints (("Goal" :expand ((boymoo-compiler::plain-symbol-part-p text 0 split))))))

(local
 (defthm character-text-starts-with-a-number-sign
   (implies (data-character-text-p text value) (equal (char text 0) #\#))
   :rule-classes :forward-chaining))

(local
 (defthm complex-text-starts-with-a-number-sign
   (implies (data-complex-text-p text) (equal (char text 0) #\#))
   :rule-classes :forward-chaining))

(local
 (defthm atom-spelling-is-a-string
   (implies (data-atom-spells-value-p text value) (stringp text))
   :rule-classes :forward-chaining))

(local
 (in-theory (disable data-symbol-spelling-p data-symbol-part-spelling-p
                     data-source-symbol-agrees-p data-character-text-p data-complex-text-p)))

(defthmd data-atom-spelling-fits-storage
  (implies (data-atom-spells-value-p text value)
           (and (data-atom-storage-input-p text) (not (equal (char text 0) #\())))
  :hints (("Goal" :use ((:instance canonical-symbol-spelling-starts-with-a-symbol-byte
                                   (split (boymoo-compiler::symbol-separator text))
                                   (package (symbol-package-name value)) (name (symbol-name value)))
                        (:instance data-canonical-symbol-denotes-source-symbol
                                   (split (boymoo-compiler::symbol-separator text)) (symbol value))
                        (:instance data-related-source-symbol-fits-storage (symbol value))
                        (:instance data-decode-canonical-delimited-text
                                   (start 0) (end (length text)) (characters (coerce value 'list))))
                  :in-theory (disable data-related-source-symbol-fits-storage))))

; A dot is allowed only after one or more elements. The remainder of
; a dotted list has one atomic, nonempty tail.
(defun data-parsed-datum-spells-value-p (kind parsed value after-item)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :datum) 1 0))))
  (cond ((eq kind :datum)
         (if (consp parsed)
             (and (consp value) (data-parsed-datum-spells-value-p :items parsed value nil))
           (data-atom-spells-value-p parsed value)))
        ((atom parsed) (and (null parsed) (null value)))
        ((equal (car parsed) ".")
         (and after-item (consp (cdr parsed)) (null (cddr parsed))
              (atom value) value (not (equal (cadr parsed) boymoo-compiler::*nil-name*))
              (data-atom-spells-value-p (cadr parsed) value)))
        (t (and (consp value)
                (data-parsed-datum-spells-value-p :datum (car parsed) (car value) nil)
                (data-parsed-datum-spells-value-p :items (cdr parsed) (cdr value) t)))))

(defthmd data-parsed-datum-spelling-fits-storage
  (implies (data-parsed-datum-spells-value-p kind parsed value after-item)
           (and (data-datum-storage-input-p kind parsed) (data-datum-token-keys-p kind parsed)))
  :hints (("Goal" :induct (data-parsed-datum-spells-value-p kind parsed value after-item)
                  :in-theory (e/d (data-atom-spelling-fits-storage)
                                 (data-atom-spells-value-p data-atom-storage-input-p)))))

(defun data-constant-spells-value-p (text events parsed value)
  (if (consp value)
      (and (stringp text) (equal (char text 0) #\()
           (mv-let (ok forms) (data-reader-events events text 0 (length text) nil nil nil)
             (and ok (equal forms (list parsed))))
           (data-parsed-datum-spells-value-p :datum parsed value nil))
    (data-atom-spells-value-p text value)))

(defthmd data-constant-spelling-fits-storage
  (implies (data-constant-spells-value-p text events parsed value)
           (and (data-constant-storage-input-p text) (data-constant-token-key-p text)))
  :hints (("Goal" :use ((:instance data-atom-spelling-fits-storage)
                        (:instance data-parsed-datum-spelling-fits-storage (kind :datum) (after-item nil))
                        data-read-constant-from-spans)
                  :in-theory (disable data-atom-spells-value-p data-parsed-datum-spells-value-p
                                      data-datum-storage-input-p data-datum-token-keys-p data-reader-events
                                      boymoo-compiler::read-lines data-atom-storage-input-p mv-nth))))
