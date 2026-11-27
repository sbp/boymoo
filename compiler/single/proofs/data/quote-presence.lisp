(in-package "BOYMOO-PROOFS")

(include-book "constant-writer")
(include-book "quote-visits")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set data-table-p
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-part
                     boymoo-compiler::decode-symbol-part boymoo-compiler::table-get
                     boymoo-compiler::table-put boymoo-compiler::read-lines
                     boymoo-compiler::data-remember boymoo-compiler::data-bucket-add
                     boymoo-compiler::data-integer-limbs boymoo-compiler::data-word
                     boymoo-compiler::data-words boymoo-compiler::data-integer-value
                     boymoo-compiler::find-char boymoo-compiler::aligned-size
                     data-rational-text-p data-rational-text-value data-complex-text-p
                     data-character-text-p data-delimited-text-p char length subseq ash)))

(local
 (defthm integer-writer-returns-an-entry
   (car (boymoo-compiler::data-write-integer value width block))))

(local
 (defthm two-field-writer-returns-an-entry
   (car (boymoo-compiler::data-fields type first second block))))

(local
 (defthm text-writer-returns-an-entry
   (car (boymoo-compiler::data-text type text block))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-word)))))

(local
 (in-theory (disable boymoo-compiler::data-write-integer boymoo-compiler::data-fields
                     boymoo-compiler::data-text)))

(local
 (defthm rational-spelling-has-a-writer-entry
   (implies (data-rational-text-p text)
            (car (boymoo-compiler::data-rational text block)))
   :hints (("Goal" :use data-rational-text-allocates-normalized-fields
                   :in-theory (disable boymoo-compiler::data-rational mv-nth)))))

(local
 (defthm complex-spelling-has-a-writer-entry
   (implies (data-complex-text-p text)
            (car (boymoo-compiler::data-number text block)))
   :hints (("Goal" :use data-complex-text-allocates-normalized-fields
                   :in-theory (disable boymoo-compiler::data-number boymoo-compiler::data-rational mv-nth)))))

(local
 (defthm character-spelling-selects-the-character-writer
   (implies (data-character-text-p text value)
            (and (equal (length text) 4) (equal (char text 0) #\#) (equal (char text 1) #\\)))
   :hints (("Goal" :in-theory (enable data-character-text-p)))))

(local
 (defthm complex-spelling-selects-the-complex-writer
   (implies (data-complex-text-p text)
            (and (equal (char text 0) #\#) (equal (char text 1) #\C)))
   :hints (("Goal" :in-theory (enable data-complex-text-p)))))

(local
 (defthm rational-spelling-selects-an-entry
   (implies (and (data-rational-text-p text) (not (equal (char text 0) #\#)))
            (car (boymoo-compiler::data-number text block)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-rational)))))

(local
 (defthm non-symbol-atom-spelling-has-a-writer-entry
   (implies (and (data-atom-spells-value-p text value) (not (symbolp value)))
            (mv-nth 0 (boymoo-compiler::data-atom text packages state-data)))
   :hints (("Goal" :use (character-spelling-selects-the-character-writer
                         complex-spelling-selects-the-complex-writer)
                   :in-theory (disable boymoo-compiler::data-symbol boymoo-compiler::data-number
                                       boymoo-compiler::data-rational
                                       data-symbol-spelling-p boymoo-compiler::hex-byte)))))

(local
 (in-theory (disable data-atom-spells-value-p boymoo-compiler::data-atom
                     boymoo-compiler::data-number boymoo-compiler::data-rational)))

(local
 (defthm list-cells-return-an-entry
   (implies (and (integerp (car block)) (or (consp reversed) tail))
            (mv-nth 0 (boymoo-compiler::data-list-cells reversed tail block)))
   :hints (("Goal" :induct (boymoo-compiler::data-list-cells reversed tail block)
                   :in-theory (enable boymoo-compiler::data-word)))))

(local
 (defthm block-of-sized-state-has-an-integer-offset
   (implies (data-state-sized-p state-data 80)
            (integerp (car (boymoo-compiler::data-block state-data))))
   :hints (("Goal" :in-theory (enable data-state-sized-p data-block-sized-p)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm spelled-atom-token-is-a-string
   (implies (data-atom-spells-value-p text value) (stringp text))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-atom-spells-value-p)))))

(local
 (defthm spelled-list-value-has-a-list-form
   (implies (and (consp value) (data-parsed-datum-spells-value-p :datum parsed value nil))
            (consp parsed))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-atom-spells-value-p)))))

(local
 (defun spelled-list-entry-induction (kind parsed value packages state-data reversed)
   (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :datum) 1 0))))
   (if (eq kind :datum)
       (if (consp parsed)
           (spelled-list-entry-induction :items parsed value packages state-data nil)
         (list value packages state-data reversed))
     (if (or (atom parsed) (equal (car parsed) "."))
         (list value packages state-data reversed)
       (mv-let (word next) (boymoo-compiler::data-datum (car parsed) packages state-data)
         (spelled-list-entry-induction :items (cdr parsed) (cdr value) packages next (cons word reversed)))))))

(local
 (defthm spelled-datum-list-has-a-writer-entry
   (implies (and (data-state-sized-p state-data 80)
                 (data-parsed-datum-spells-value-p kind parsed value (consp reversed))
                 (if (eq kind :datum) (consp parsed) t))
            (if (eq kind :datum)
                (mv-nth 0 (boymoo-compiler::data-datum parsed packages state-data))
              (mv-nth 0 (boymoo-compiler::data-list-datum parsed packages state-data reversed))))
   :rule-classes nil
   :hints (("Goal" :induct (spelled-list-entry-induction kind parsed value packages state-data reversed)
                   :expand ((:free (mode after-item) (data-parsed-datum-spells-value-p mode parsed value after-item))
                            (boymoo-compiler::data-datum parsed packages state-data)
                            (boymoo-compiler::data-list-datum nil packages state-data reversed)
                            (boymoo-compiler::data-list-datum parsed packages state-data reversed))
                   :in-theory (e/d (data-atom-spelling-fits-storage data-parsed-datum-spelling-fits-storage)
                                   (mv-nth data-parsed-datum-spells-value-p boymoo-compiler::data-datum
                                    boymoo-compiler::data-list-datum data-state-sized-p data-block-sized-p
                                    boymoo-compiler::data-list-cells
                                    boymoo-compiler::data-with-block boymoo-compiler::data-block))))))

(defthmd data-spelled-non-symbol-constant-has-an-index-entry
  (implies (and (data-constant-spells-value-p text events parsed value) (not (symbolp value))
                (data-state-sized-p state-data 80) (data-table-p (cadr state-data) 12))
           (boymoo-compiler::index-get text (cadr (boymoo-compiler::data-constant text packages state-data))))
  :hints (("Goal" :use ((:instance spelled-datum-list-has-a-writer-entry (kind :datum) (reversed nil))
                        non-symbol-atom-spelling-has-a-writer-entry
                        data-spelled-constant-index-lookup-is-writer-entry)
                  :in-theory (disable data-state-sized-p data-reader-events data-parsed-datum-spells-value-p
                                      non-symbol-atom-spelling-has-a-writer-entry
                                      boymoo-compiler::data-constant boymoo-compiler::data-datum))))

(local
 (in-theory (disable data-constant-spells-value-p data-state-sized-p boymoo-compiler::data-constant
                     boymoo-compiler::data-atom boymoo-compiler::data-note-symbol boymoo-compiler::data-formals
                     boymoo-compiler::data-datum boymoo-compiler::declaration-list
                     boymoo-compiler::data-term boymoo-compiler::data-terms
                     data-term-constant-keys-p data-term-storage-input-p)))

(local
 (defthm missing-entry-in-appended-visits
   (iff (member-equal nil (append first rest))
        (or (member-equal nil first) (member-equal nil rest)))))

(defthmd data-term-visits-record-spelled-non-symbol-constant
  (implies (and (data-constant-spells-value-p query events parsed-datum value) (not (symbolp value))
                (data-term-storage-input-p kind parsed depth) (data-term-constant-keys-p kind parsed depth)
                (data-state-sized-p state-data 80) (data-table-p (cadr state-data) 12))
           (not (member-equal nil (data-term-quote-visits kind parsed query packages state-data depth))))
  :hints (("Goal" :induct (data-term-quote-visits kind parsed query packages state-data depth)
                  :in-theory (enable data-spelled-non-symbol-constant-has-an-index-entry)
                  :expand ((:free (mode) (data-term-storage-input-p mode parsed depth))
                           (:free (mode) (data-term-constant-keys-p mode parsed depth))
                           (boymoo-compiler::data-term parsed packages state-data depth)))))

(local
 (in-theory (disable data-term-quote-visits boymoo-compiler::data-definitions)))

(defthmd data-definition-visits-record-spelled-non-symbol-constant
  (implies (and (data-constant-spells-value-p query events parsed-datum value) (not (symbolp value))
                (data-definitions-storage-input-p definitions) (data-definition-constant-keys-p definitions)
                (data-state-sized-p state-data 80) (data-table-p (cadr state-data) 12))
           (not (member-equal nil (data-definition-quote-visits definitions query packages state-data))))
  :hints (("Goal" :induct (data-definition-quote-visits definitions query packages state-data)
                  :in-theory (enable data-term-visits-record-spelled-non-symbol-constant))))

(local
 (in-theory (disable data-definition-quote-visits data-definition-constant-keys-p data-definitions-storage-input-p
                     data-datum-storage-input-p data-datum-token-keys-p boymoo-compiler::data-program-symbols)))

(defthmd data-program-visits-record-spelled-non-symbol-constant
  (implies (and (data-constant-spells-value-p query events parsed-datum value) (not (symbolp value))
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-state-sized-p state-data 80) (data-table-p (cadr state-data) 12))
           (not (member-equal nil (data-program-quote-visits lines query packages state-data))))
  :hints (("Goal" :induct (data-program-quote-visits lines query packages state-data)
                  :in-theory (enable data-definition-visits-record-spelled-non-symbol-constant))
          ("Subgoal *1/2" :expand ((data-program-storage-input-p (list (car lines)))
                                   (data-program-constant-keys-p (list (car lines)))))))

(local
 (in-theory (disable data-program-quote-visits data-program-storage-input-p data-program-constant-keys-p
                     boymoo-compiler::data-packages boymoo-compiler::data-package-numbers)))

(local
 (defthm initial-visit-constant-index-is-a-table
   (data-table-p (cadr (mv-nth 2 (boymoo-compiler::data-initial number))) 12)))

(local (in-theory (disable boymoo-compiler::data-initial)))

(defthmd data-build-visits-record-spelled-non-symbol-constant
  (implies (and (data-constant-spells-value-p query events parsed-datum value) (not (symbolp value))
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-package-lines-storage-input-p package-lines))
           (not (member-equal nil (data-build-quote-visits lines package-lines query))))
  :hints (("Goal" :in-theory (enable data-program-visits-record-spelled-non-symbol-constant))))

(local
 (defthm nonempty-visit-count-gives-a-first-entry
   (implies (< 0 (len visits)) (member-equal (car visits) visits))))

(local
 (defthm spelled-constant-token-is-a-string
   (implies (data-constant-spells-value-p text events parsed value) (stringp text))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (data-constant-spells-value-p) (data-reader-events))))))

(defthmd data-build-records-every-spelled-non-symbol-quote
  (implies (and (data-constant-spells-value-p query events parsed-datum value) (not (symbolp value))
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-package-lines-storage-input-p package-lines)
                (boymoo-compiler::index-get
                 "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil))
                (< 0 (data-program-quote-count lines query)))
           (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build lines package-lines))))
  :hints (("Goal" :use (data-build-visits-record-spelled-non-symbol-constant
                        data-build-quote-visits-count-every-occurrence
                        (:instance data-build-retains-each-present-quote-visit
                                   (entry (car (data-build-quote-visits lines package-lines query))))
                        (:instance nonempty-visit-count-gives-a-first-entry
                                   (visits (data-build-quote-visits lines package-lines query))))
                  :in-theory (disable data-build-quote-visits data-program-quote-count boymoo-compiler::data-build
                                      nonempty-visit-count-gives-a-first-entry))))
