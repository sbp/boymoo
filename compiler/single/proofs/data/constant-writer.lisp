(in-package "BOYMOO-PROOFS")

(include-book "datum-spelling")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set data-table-p
                     boymoo-compiler::table-get boymoo-compiler::table-put
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-part
                     boymoo-compiler::decode-symbol-part boymoo-compiler::data-text
                     boymoo-compiler::data-fields boymoo-compiler::data-bucket-add
                     boymoo-compiler::data-number boymoo-compiler::hex-byte char length)))

(local
 (defthm interning-preserves-constant-index
   (equal (cadr (mv-nth 2 (boymoo-compiler::data-intern number name state-data)))
          (cadr state-data))))

(local (in-theory (disable boymoo-compiler::data-intern)))

(local
 (defthm symbol-index-lookup-is-returned-entry
   (implies (and (stringp text) (data-table-p (cadr state-data) 12)
                 (not (equal (char text 0) #\")) (not (equal (char text 0) #\#)))
            (mv-let (entry next) (boymoo-compiler::data-symbol text packages state-data)
              (implies (or (not (boymoo-compiler::index-get text (cadr state-data)))
                           entry)
                       (equal (boymoo-compiler::index-get text (cadr next)) entry))))))

(local (in-theory (disable boymoo-compiler::data-symbol)))

(defthmd data-atom-index-lookup-is-returned-entry
  (implies (and (stringp text) (data-table-p (cadr state-data) 12))
           (mv-let (entry next) (boymoo-compiler::data-atom text packages state-data)
             (equal (boymoo-compiler::index-get text (cadr next)) entry)))
  :hints (("Goal" :in-theory (disable mv-nth))))

(local
 (defthm atom-cache-hit-is-the-returned-entry
   (implies (boymoo-compiler::index-get text (cadr state-data))
            (equal (car (boymoo-compiler::data-atom text packages state-data))
                   (boymoo-compiler::index-get text (cadr state-data))))))

(local
 (in-theory (disable boymoo-compiler::data-atom boymoo-compiler::data-datum boymoo-compiler::read-lines
                     data-datum-token-keys-p)))

(defthmd data-constant-index-lookup-is-writer-entry
  (let* ((old (boymoo-compiler::index-get text (cadr state-data)))
         (constant (boymoo-compiler::data-constant text packages state-data)))
    (implies (and (data-table-p (cadr state-data) 12) (data-constant-token-key-p text))
             (equal (boymoo-compiler::index-get text (cadr constant))
                    (or old
                        (if (equal (char text 0) #\()
                            (let* ((size (length text))
                                   (forms (boymoo-compiler::read-lines text 0 size nil nil nil size)))
                              (mv-nth 0 (boymoo-compiler::data-datum (car forms) packages state-data)))
                          (mv-nth 0 (boymoo-compiler::data-atom text packages state-data)))))))
  :hints (("Goal" :in-theory (enable data-atom-index-lookup-is-returned-entry))))

(defthmd data-spelled-constant-index-lookup-is-writer-entry
  (implies (and (data-table-p (cadr state-data) 12)
                (data-constant-spells-value-p text events parsed value))
           (equal (boymoo-compiler::index-get text (cadr (boymoo-compiler::data-constant text packages state-data)))
                  (or (boymoo-compiler::index-get text (cadr state-data))
                      (if (consp value)
                          (mv-nth 0 (boymoo-compiler::data-datum parsed packages state-data))
                        (mv-nth 0 (boymoo-compiler::data-atom text packages state-data))))))
  :hints (("Goal" :use (data-constant-index-lookup-is-writer-entry
                        data-constant-spelling-fits-storage data-read-constant-from-spans
                        data-atom-spelling-fits-storage)
                  :in-theory (disable boymoo-compiler::data-constant data-atom-spells-value-p
                                      data-constant-token-key-p data-constant-storage-input-p
                                      data-reader-events data-parsed-datum-spells-value-p data-atom-storage-input-p
                                      mv-nth))))

(defthmd data-retained-constant-entry-gives-constant-map-agreement
  (let* ((entry (boymoo-compiler::index-get text (cadr before)))
         (word (proof-constant-word entry)))
    (implies (and (stringp text) word (data-constant-index-retains-p text before after)
                  (proof-value-p word value base objects packages machine))
             (proof-constant-map-p (list (cons text value)) (cadr after) base objects packages machine))))
