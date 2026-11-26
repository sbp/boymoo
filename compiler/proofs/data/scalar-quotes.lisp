(in-package "BOYMOO-PROOFS")

(include-book "scalar-constants")
(include-book "quote-presence")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set data-table-p
                     boymoo-compiler::table-get boymoo-compiler::table-put boymoo-compiler::read-lines
                     boymoo-compiler::data-constant boymoo-compiler::data-symbol boymoo-compiler::data-datum
                     boymoo-compiler::data-list-cells boymoo-compiler::data-text boymoo-compiler::data-number
                     boymoo-compiler::declaration-list boymoo-compiler::symbol-separator
                     boymoo-compiler::decode-part boymoo-compiler::decode-symbol-part char length
                     data-scalar-cache-entry-p data-scalar-quote-p data-datum-token-keys-p)))

(local
 (defthm noting-a-symbol-preserves-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data))
            (data-scalar-cache-entry-p query value
                                       (boymoo-compiler::data-note-symbol text packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-note-symbol)))

(local
 (defthm formals-preserve-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data))
            (data-scalar-cache-entry-p query value
                                       (boymoo-compiler::data-formals formals packages state-data)))
   :hints (("Goal" :induct (boymoo-compiler::data-formals formals packages state-data)))))

(local
 (defthm constant-token-key-is-text
   (implies (data-constant-token-key-p text) (stringp text))
   :rule-classes :forward-chaining))

(local (in-theory (disable boymoo-compiler::data-formals data-constant-token-key-p)))

(local
 (defthm term-pass-preserves-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data)
                 (data-term-constant-keys-p kind parsed depth))
            (data-scalar-cache-entry-p
             query value
             (if (eq kind :term)
                 (boymoo-compiler::data-term parsed packages state-data depth)
               (boymoo-compiler::data-terms parsed packages state-data depth))))
   :rule-classes nil
   :hints (("Goal" :induct (data-term-state-induction kind parsed packages state-data depth)))))

(local
 (defthm term-preserves-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data)
                 (data-term-constant-keys-p :term parsed depth))
            (data-scalar-cache-entry-p query value
                                       (boymoo-compiler::data-term parsed packages state-data depth)))
   :hints (("Goal" :use ((:instance term-pass-preserves-scalar-cache-entry (kind :term)))
                   :in-theory (disable boymoo-compiler::data-term data-term-constant-keys-p)))))

(local (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms data-term-constant-keys-p)))

(local
 (defthm definitions-preserve-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data)
                 (data-definition-constant-keys-p definitions))
            (data-scalar-cache-entry-p
             query value (boymoo-compiler::data-definitions definitions packages state-data)))
   :hints (("Goal" :induct (boymoo-compiler::data-definitions definitions packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-definitions data-definition-constant-keys-p)))

(local
 (defthm program-preserves-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data)
                 (data-program-constant-keys-p lines))
            (data-scalar-cache-entry-p
             query value (boymoo-compiler::data-program-symbols lines packages state-data)))
   :hints (("Goal" :induct (boymoo-compiler::data-program-symbols lines packages state-data)))))

(local
 (defthm adding-a-bucket-entry-keeps-the-constant-index
   (equal (cadr (boymoo-compiler::data-bucket-add number name name-word symbol-word state-data))
          (cadr state-data))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-cell)))))

(local (in-theory (disable boymoo-compiler::data-bucket-add)))

(local
 (defthm changing-the-block-keeps-the-scalar-cache-entry
   (equal (data-scalar-cache-entry-p query value (boymoo-compiler::data-with-block block state-data))
          (data-scalar-cache-entry-p query value state-data))
   :hints (("Goal" :in-theory (enable data-scalar-cache-entry-p)))))

(local
 (defthm recording-an-import-keeps-the-scalar-cache-entry
   (equal (data-scalar-cache-entry-p
           query value (boymoo-compiler::data-bucket-add
                        number name name-word symbol-word (cons names (cdr state-data))))
          (data-scalar-cache-entry-p query value state-data))
   :hints (("Goal" :in-theory (enable data-scalar-cache-entry-p)))))

(local (in-theory (disable boymoo-compiler::data-with-block boymoo-compiler::text-hash)))

(local
 (defthm imports-preserve-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data))
            (data-scalar-cache-entry-p
             query value
             (mv-nth 1 (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed))))
   :hints (("Goal" :induct (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed)))))

(local (in-theory (disable boymoo-compiler::data-imports)))

(local
 (defthm package-declarations-preserve-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data))
            (data-scalar-cache-entry-p
             query value
             (mv-nth 1 (boymoo-compiler::data-package-declarations
                        lines packages declared declarations state-data names))))
   :hints (("Goal" :induct (boymoo-compiler::data-package-declarations
                           lines packages declared declarations state-data names)))))

(local (in-theory (disable boymoo-compiler::data-package-declarations boymoo-compiler::data-package-vectors)))

(local
 (defthm package-vectors-keep-the-scalar-cache-entry
   (equal (data-scalar-cache-entry-p
           query value (mv-nth 1 (boymoo-compiler::data-package-vectors
                                  names packages declarations state-data reversed)))
          (data-scalar-cache-entry-p query value state-data))
   :hints (("Goal" :in-theory (enable data-scalar-cache-entry-p)))))

(local
 (defthm packages-preserve-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value)
                 (data-table-p (cadr state-data) 12)
                 (data-scalar-cache-entry-p query value state-data))
            (data-scalar-cache-entry-p
             query value
             (mv-nth 1 (boymoo-compiler::data-packages lines number packages state-data reversed))))))

(local
 (defthm initial-constant-index-is-a-table
   (data-table-p (cadr (mv-nth 2 (boymoo-compiler::data-initial number))) 12)
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-with-block boymoo-compiler::text-hash)))))

(local
 (defthm scalar-spelling-is-distinct-from-initial-symbols
   (implies (data-scalar-quote-p query value)
            (and (stringp query)
                 (not (equal query boymoo-compiler::*nil-name*))
                 (not (equal query "COMMON-LISP::T"))))
   :hints (("Goal" :use ((:instance data-scalar-quote-spelling-selects-its-writer (text query)))))))

(local
 (defthm initial-scalar-cache-has-no-entry
   (implies (data-scalar-quote-p query value)
            (data-scalar-cache-entry-p query value (mv-nth 2 (boymoo-compiler::data-initial number))))
   :hints (("Goal" :in-theory (e/d (data-scalar-cache-entry-p)
                                  ((:executable-counterpart boymoo-compiler::index-set)))))))

(local
 (in-theory (disable boymoo-compiler::data-initial boymoo-compiler::data-packages
                     boymoo-compiler::data-package-numbers boymoo-compiler::data-program-symbols
                     boymoo-compiler::data-bucket-vector boymoo-compiler::data-write
                     data-program-constant-keys-p)))

(local
 (defthm rebuild-with-just-the-constant-index-keeps-the-scalar-cache-entry
   (equal (data-scalar-cache-entry-p query value (list nil (cadr state-data)))
          (data-scalar-cache-entry-p query value state-data))
   :hints (("Goal" :in-theory (enable data-scalar-cache-entry-p)))))

(local
 (defthm built-image-keeps-the-scalar-cache-entry
   (implies (and (data-scalar-quote-p query value) (data-program-constant-keys-p lines)
                 (boymoo-compiler::index-get
                  "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
            (data-scalar-cache-entry-p
             query value (list nil (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))))
   :rule-classes nil))

(defthmd data-build-scalar-entry-is-absent-or-exact
  (implies (and (data-scalar-quote-p query value) (data-program-constant-keys-p lines)
                (boymoo-compiler::index-get
                 "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
           (let ((entry (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))))
             (or (not entry) (equal entry (data-scalar-quote-entry value)))))
  :hints (("Goal" :use built-image-keeps-the-scalar-cache-entry
                  :in-theory (e/d (data-scalar-cache-entry-p) (boymoo-compiler::data-build)))))

(local
 (defthm scalar-spelling-is-a-non-symbol-constant-spelling
   (implies (data-scalar-quote-p query value)
            (and (not (symbolp value)) (data-constant-spells-value-p query nil nil value)))
   :hints (("Goal" :in-theory (e/d (data-scalar-quote-p)
                                  (data-atom-spells-value-p data-reader-events
                                   data-parsed-datum-spells-value-p))))))

(defthmd data-build-records-every-exact-scalar-quote
  (implies (and (data-scalar-quote-p query value)
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-package-lines-storage-input-p package-lines)
                (boymoo-compiler::index-get
                 "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil))
                (< 0 (data-program-quote-count lines query)))
           (equal (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))
                  (data-scalar-quote-entry value)))
  :hints (("Goal" :use (data-build-scalar-entry-is-absent-or-exact
                        (:instance data-build-records-every-spelled-non-symbol-quote
                                   (events nil) (parsed-datum nil))
                        scalar-spelling-is-a-non-symbol-constant-spelling)
                  :in-theory (disable boymoo-compiler::data-build data-scalar-quote-entry
                                      data-constant-spells-value-p data-program-storage-input-p
                                      data-package-lines-storage-input-p data-program-quote-count))))

(defthmd data-build-scalar-quote-has-its-source-value
  (implies (and (data-scalar-quote-p query value)
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-package-lines-storage-input-p package-lines)
                (boymoo-compiler::index-get
                 "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil))
                (< 0 (data-program-quote-count lines query)))
           (proof-constant-map-p (list (cons query value))
                                 (mv-nth 1 (boymoo-compiler::data-build lines package-lines))
                                 base objects packages machine))
  :hints (("Goal" :use (data-build-records-every-exact-scalar-quote
                        (:instance data-view-of-immediate-integer (integer value))
                        (:instance data-view-of-character (byte value)))
                  :in-theory (e/d (data-scalar-quote-p)
                                 (boymoo-compiler::data-build proof-value-p proof-immediate-integer-p
                                  proof-integer-word data-atom-spells-value-p
                                  data-program-storage-input-p data-package-lines-storage-input-p
                                  data-program-quote-count)))))
