(in-package "BOYMOO-PROOFS")

(include-book "constants")
(include-book "datum-spelling")

(logic)
(set-verify-guards-eagerness 0)

(defun data-scalar-quote-p (text value)
  (and (or (proof-immediate-integer-p value) (characterp value))
       (data-atom-spells-value-p text value)))

(defun data-scalar-quote-entry (value)
  (if (characterp value) (proof-character-word value) (cons :integer value)))

(defun data-scalar-cache-entry-p (query value state-data)
  (let ((entry (boymoo-compiler::index-get query (cadr state-data))))
    (or (not entry) (equal entry (data-scalar-quote-entry value)))))

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set data-table-p
                     boymoo-compiler::table-get boymoo-compiler::table-put boymoo-compiler::read-lines
                     boymoo-compiler::symbol-separator boymoo-compiler::find-char
                     boymoo-compiler::data-intern boymoo-compiler::data-bucket-add
                     boymoo-compiler::data-number boymoo-compiler::data-text boymoo-compiler::hex-byte
                     boymoo-compiler::decode-part boymoo-compiler::decode-symbol-part
                     data-symbol-spelling-p data-integer-text-p data-text-integer
                     data-constant-storage-input-p data-delimited-text-p char length)))

(local
 (defthm integral-rational-spelling-has-decimal-value
   (implies (and (data-rational-text-p text) (integerp (data-rational-text-value text)))
            (and (data-integer-text-p text 0 (length text))
                 (equal (data-text-integer text 0 (length text)) (data-rational-text-value text))))))

(defthmd data-scalar-quote-spelling-selects-its-writer
  (implies (data-scalar-quote-p text value)
           (and (stringp text) (not (equal (char text 0) #\())
                (or (equal (char text 0) #\#) (not (boymoo-compiler::symbol-separator text)))
                (if (characterp value)
                    (data-character-text-p text value)
                  (and (data-integer-text-p text 0 (length text)) (proof-immediate-integer-p value)
                       (equal (data-text-integer text 0 (length text)) value)))))
  :hints (("Goal" :in-theory (disable data-rational-text-p data-rational-text-value
                                      data-hex-digit-character))))

(local
 (defthm adding-a-bucket-entry-frames-the-constant-index
   (equal (cadr (boymoo-compiler::data-bucket-add number name name-word symbol-word state-data))
          (cadr state-data))
   :hints (("Goal" :in-theory (e/d (boymoo-compiler::data-bucket-add)
                                  (boymoo-compiler::data-cell))))))

(local
 (defthm interning-frames-the-completed-constant-index
   (equal (cadr (mv-nth 2 (boymoo-compiler::data-intern number name state-data))) (cadr state-data))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-intern)))))

(local
 (defthm scalar-spelling-gives-a-text-key
   (implies (data-scalar-quote-p text value) (stringp text))
   :rule-classes :forward-chaining))

(local (in-theory (disable data-scalar-quote-p data-atom-spells-value-p data-scalar-quote-entry)))

(defthmd data-noting-a-symbol-keeps-a-scalar-index-lookup
  (implies (and (data-scalar-quote-p query value) (data-table-p (cadr state-data) 12))
           (equal (boymoo-compiler::index-get query
                                              (cadr (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data))))
                  (boymoo-compiler::index-get query (cadr state-data))))
  :hints (("Goal" :use ((:instance data-scalar-quote-spelling-selects-its-writer (text query)))
                  :in-theory (disable data-character-text-p))))

(local (in-theory (disable boymoo-compiler::data-symbol)))

(defthmd data-atom-on-a-different-key-keeps-scalar-index-lookup
  (implies (and (stringp text) (not (equal query text)) (data-scalar-quote-p query value)
                (data-table-p (cadr state-data) 12))
           (equal (boymoo-compiler::index-get query (cadr (mv-nth 1 (boymoo-compiler::data-atom text packages state-data))))
                  (boymoo-compiler::index-get query (cadr state-data))))
  :hints (("Goal" :use data-noting-a-symbol-keeps-a-scalar-index-lookup)))

(defthmd data-scalar-writer-records-exact-entry
  (implies (and (data-scalar-quote-p query value) (data-table-p (cadr state-data) 12)
                (data-scalar-cache-entry-p query value state-data))
           (equal (boymoo-compiler::index-get query (cadr (mv-nth 1 (boymoo-compiler::data-atom query packages state-data))))
                  (data-scalar-quote-entry value)))
  :hints (("Goal" :use ((:instance data-scalar-quote-spelling-selects-its-writer (text query))
                        (:instance data-constant-records-canonical-integer (text query))
                        (:instance data-constant-records-canonical-character (text query) (byte value)))
                  :in-theory (e/d (data-scalar-quote-entry)
                                 (boymoo-compiler::data-atom proof-character-word data-character-text-p
                                  proof-immediate-integer-p)))))

(defthm data-atom-preserves-exact-scalar-cache-entry
  (implies (and (stringp text) (data-scalar-quote-p query value)
                (data-scalar-cache-entry-p query value state-data) (data-table-p (cadr state-data) 12))
           (data-scalar-cache-entry-p query value (mv-nth 1 (boymoo-compiler::data-atom text packages state-data))))
  :hints (("Goal" :cases ((equal text query))
                  :use (data-scalar-writer-records-exact-entry data-atom-on-a-different-key-keeps-scalar-index-lookup)
                  :in-theory (disable boymoo-compiler::data-atom))))

(defthm data-symbol-preserves-exact-scalar-cache-entry
  (implies (and (data-scalar-quote-p query value) (data-scalar-cache-entry-p query value state-data)
                (data-table-p (cadr state-data) 12))
           (data-scalar-cache-entry-p query value (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data))))
  :hints (("Goal" :use data-noting-a-symbol-keeps-a-scalar-index-lookup)))

(local
 (defthm scalar-cache-entry-depends-only-on-the-constant-index
   (equal (data-scalar-cache-entry-p
           query value (list* (car state-data) (cadr state-data) other-names block))
          (data-scalar-cache-entry-p query value state-data))))

(local
 (in-theory (disable data-scalar-cache-entry-p boymoo-compiler::data-atom
                     boymoo-compiler::data-list-cells data-datum-token-keys-p mv-nth)))

(local
 (defthm datum-pass-preserves-exact-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value) (data-scalar-cache-entry-p query value state-data)
                 (data-table-p (cadr state-data) 12) (data-datum-token-keys-p kind parsed))
            (data-scalar-cache-entry-p query value
                                      (mv-nth 1 (if (eq kind :datum)
                                                    (boymoo-compiler::data-datum parsed packages state-data)
                                                  (boymoo-compiler::data-list-datum parsed packages state-data reversed)))))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-state-induction kind parsed packages state-data reversed)
                   :in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum)
                   :expand ((boymoo-compiler::data-datum parsed packages state-data)
                            (boymoo-compiler::data-list-datum parsed packages state-data reversed)
                            (:free (mode) (data-datum-token-keys-p mode parsed)))))))

(defthm data-datum-preserves-exact-scalar-cache-entry
  (implies (and (data-scalar-quote-p query value) (data-scalar-cache-entry-p query value state-data)
                (data-table-p (cadr state-data) 12) (data-datum-token-keys-p :datum parsed))
           (data-scalar-cache-entry-p query value (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data))))
  :hints (("Goal" :use ((:instance datum-pass-preserves-exact-scalar-cache-entry (kind :datum) (reversed nil)))
                  :in-theory (disable boymoo-compiler::data-datum))))

(local
 (defthm remembering-a-different-key-preserves-the-scalar-cache-entry
   (implies (and (stringp text) (stringp query) (not (equal text query))
                 (data-table-p (cadr state-data) 12))
            (equal (data-scalar-cache-entry-p query value (boymoo-compiler::data-remember text entry state-data))
                   (data-scalar-cache-entry-p query value state-data)))
   :hints (("Goal" :in-theory (enable data-scalar-cache-entry-p)))))

(defthm data-constant-preserves-exact-scalar-cache-entry
  (implies (and (data-scalar-quote-p query value) (data-scalar-cache-entry-p query value state-data)
                (data-table-p (cadr state-data) 12) (data-constant-token-key-p text))
           (data-scalar-cache-entry-p query value (boymoo-compiler::data-constant text packages state-data)))
  :hints (("Goal" :use ((:instance data-scalar-quote-spelling-selects-its-writer (text query)))
                  :cases ((equal text query))
                  :in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-remember
                                      data-character-text-p))))
