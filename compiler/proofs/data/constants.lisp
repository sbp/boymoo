(in-package "BOYMOO-PROOFS")

(include-book "reader")
(include-book "static-values")
(include-book "tables")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable char boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::hex-byte data-table-p length)))

(local
 (defthm no-outside-character-in-decimal-digits
   (implies (and (data-decimal-digits-p text start count)
                 (or (< (char-code wanted) 48) (< 57 (char-code wanted))))
            (equal (boymoo-compiler::find-char text start count wanted) nil))
   :hints (("Goal" :induct (boymoo-compiler::find-char text start count wanted)))))

(local
 (defthm no-outside-character-in-integer-text
   (implies (and (data-integer-text-p text 0 (length text))
                 (not (equal wanted #\-))
                 (or (< (char-code wanted) 48) (< 57 (char-code wanted))))
            (equal (boymoo-compiler::find-char text 0 (length text) wanted) nil))
   :hints (("Goal" :expand ((boymoo-compiler::find-char text 0 (length text) wanted))
                   :in-theory (disable length)))))

(local
 (defthm canonical-integer-does-not-start-with-reader-delimiter
   (implies (data-integer-text-p text 0 (length text))
            (and (stringp text)
                 (not (equal (char text 0) #\")) (not (equal (char text 0) #\#))
                 (not (equal (char text 0) #\|)) (not (equal (char text 0) #\())))
   :rule-classes :forward-chaining
   :hints (("Goal" :expand ((data-decimal-digits-p text 0 (length text)))
                   :in-theory (disable length)))))

(local
 (defthm canonical-integer-is-not-symbol-text
   (implies (data-integer-text-p text 0 (length text))
            (not (boymoo-compiler::symbol-separator text)))
   :hints (("Goal" :use ((:instance no-outside-character-in-integer-text (wanted #\:)))
                   :in-theory (disable data-integer-text-p boymoo-compiler::find-char
                                       no-outside-character-in-integer-text)))))

(defthmd data-number-immediate-spelling
  (let ((value (data-text-integer text 0 (length text))))
    (implies (and (data-integer-text-p text 0 (length text))
                  (proof-immediate-integer-p value))
             (equal (mv-list 2 (boymoo-compiler::data-number text block))
                    (list (cons :integer value) block))))
  :hints (("Goal" :in-theory (e/d (data-read-canonical-integer)
                                 (data-integer-text-p data-text-integer
                                  boymoo-compiler::find-char boymoo-compiler::data-integer-value
                                  length)))))

(local
 (in-theory (disable boymoo-compiler::data-number boymoo-compiler::data-symbol
                     boymoo-compiler::symbol-separator boymoo-compiler::read-lines
                     boymoo-compiler::data-datum data-hex-digit-character floor mod)))

(defthmd data-constant-records-canonical-integer
  (let ((old (boymoo-compiler::index-get text (cadr state-data)))
        (value (data-text-integer text 0 (length text))))
    (implies (and (data-integer-text-p text 0 (length text)) (proof-immediate-integer-p value)
                  (data-table-p (cadr state-data) 12)
                  (or (not old) (equal old (cons :integer value))))
             (equal (boymoo-compiler::index-get
                     text (cadr (boymoo-compiler::data-constant text packages state-data)))
                    (cons :integer value))))
  :hints (("Goal" :in-theory (e/d (data-number-immediate-spelling)
                                 (data-integer-text-p data-text-integer
                                  proof-immediate-integer-p length)))))

(defthmd data-constant-records-canonical-character
  (let ((old (boymoo-compiler::index-get text (cadr state-data))))
    (implies (and (data-character-text-p text byte) (data-table-p (cadr state-data) 12)
                  (or (not old) (equal old (proof-character-word byte))))
             (equal (boymoo-compiler::index-get
                     text (cadr (boymoo-compiler::data-constant text packages state-data)))
                    (proof-character-word byte))))
  :hints (("Goal" :use data-read-canonical-character
                  :in-theory (disable length boymoo-compiler::printable-byte-p))))

(defthmd data-immediate-constant-map-agreement
  (let ((old (boymoo-compiler::index-get text (cadr state-data)))
        (value (data-text-integer text 0 (length text))))
    (implies (and (data-integer-text-p text 0 (length text)) (proof-immediate-integer-p value)
                  (data-table-p (cadr state-data) 12)
                  (or (not old) (equal old (cons :integer value))))
             (proof-constant-map-p
              (list (cons text value))
              (cadr (boymoo-compiler::data-constant text package-index state-data))
              base objects packages machine)))
  :hints (("Goal" :use ((:instance data-constant-records-canonical-integer (packages package-index))
                       (:instance data-view-of-immediate-integer
                                  (integer (data-text-integer text 0 (length text)))))
                  :in-theory (disable boymoo-compiler::data-constant data-text-integer
                                      data-integer-text-p proof-value-p proof-integer-word))))

(defthmd data-character-constant-map-agreement
  (let ((old (boymoo-compiler::index-get text (cadr state-data))))
    (implies (and (data-character-text-p text byte) (data-table-p (cadr state-data) 12)
                  (or (not old) (equal old (proof-character-word byte))))
             (proof-constant-map-p
              (list (cons text byte))
              (cadr (boymoo-compiler::data-constant text package-index state-data))
              base objects packages machine)))
  :hints (("Goal" :use ((:instance data-constant-records-canonical-character (packages package-index))
                       data-view-of-character)
                  :in-theory (disable boymoo-compiler::data-constant proof-value-p))))

(defthmd data-normalized-fraction-allocates-type-four
  (let* ((end (length text))
         (slash (boymoo-compiler::find-char text 0 end #\/))
         (den-start (1+ slash))
         (num (data-text-integer text 0 slash))
         (den (data-text-integer text den-start end)))
    (implies (and slash (data-integer-text-p text 0 slash) (data-integer-text-p text den-start end)
                  (proof-immediate-integer-p num) (proof-immediate-integer-p den)
                  (not (equal num 0)) (< 1 den) (equal (denominator (/ num den)) den))
             (equal (mv-list 2 (boymoo-compiler::data-rational text block))
                    (mv-list 2 (boymoo-compiler::data-fields 4 (cons :integer num) (cons :integer den)
                                                           block)))))
  :hints (("Goal" :in-theory (e/d (data-read-canonical-integer)
                                 (data-integer-text-p data-text-integer boymoo-compiler::data-fields
                                  boymoo-compiler::find-char boymoo-compiler::data-integer-value)))))
