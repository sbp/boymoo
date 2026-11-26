(in-package "BOYMOO-PROOFS")

(include-book "constant-writer")

(logic)
(set-verify-guards-eagerness 0)

(defun data-symbol-home-available-p (number name state-data)
  (let ((binding (data-name-table-lookup number name state-data)))
    (or (not binding) (and (car binding) (not (eq (car binding) :import))))))

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::table-get boymoo-compiler::table-put data-table-p
                     boymoo-compiler::data-bucket-add boymoo-compiler::data-text
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                     boymoo-compiler::text-hash char length)))

(defthmd data-intern-returns-a-symbol-entry-for-an-available-home
  (implies (data-symbol-home-available-p number name state-data)
           (mv-nth 0 (boymoo-compiler::data-intern number name state-data))))

(local
 (defthm canonical-symbol-part-starts-outside-the-number-and-string-cases
   (implies (data-symbol-spelling-p text split package name)
            (not (member-equal (char text 0) '(#\( #\" #\#))))
   :hints (("Goal" :expand ((boymoo-compiler::plain-symbol-part-p text 0 split))))))

(local
 (defthm a-spelled-source-symbol-selects-its-home-name-reader
   (implies (and (symbolp symbol) (data-atom-spells-value-p text symbol))
            (and (data-source-symbol-agrees-p text symbol)
                 (not (member-equal (char text 0) '(#\( #\" #\#)))))
   :hints (("Goal" :use ((:instance data-canonical-symbol-denotes-source-symbol
                                    (split (boymoo-compiler::symbol-separator text)))
                         (:instance canonical-symbol-part-starts-outside-the-number-and-string-cases
                                    (split (boymoo-compiler::symbol-separator text))
                                    (package (symbol-package-name symbol)) (name (symbol-name symbol))))
                   :in-theory (disable data-symbol-spelling-p data-source-symbol-agrees-p
                                       canonical-symbol-part-starts-outside-the-number-and-string-cases)))))

(local
 (in-theory (disable data-atom-spells-value-p data-symbol-home-available-p
                     boymoo-compiler::data-intern boymoo-compiler::data-remember
                     boymoo-compiler::data-number boymoo-compiler::hex-byte)))

(defthmd data-spelled-symbol-constant-has-an-entry-with-available-home
  (let* ((old (boymoo-compiler::index-get text (cadr state-data)))
         (number (boymoo-compiler::index-get (symbol-package-name symbol) packages)))
    (implies (and (symbolp symbol) (data-atom-spells-value-p text symbol) (data-table-p (cadr state-data) 12)
                  (or old (and number (data-symbol-home-available-p number (symbol-name symbol) state-data))))
             (boymoo-compiler::index-get text (cadr (boymoo-compiler::data-constant text packages state-data)))))
  :hints (("Goal" :use (a-spelled-source-symbol-selects-its-home-name-reader
                        (:instance data-spelled-constant-index-lookup-is-writer-entry (value symbol)
                                   (events nil) (parsed nil))
                        (:instance data-intern-returns-a-symbol-entry-for-an-available-home
                                   (number (boymoo-compiler::index-get (symbol-package-name symbol) packages))
                                   (name (symbol-name symbol))))
                  :in-theory (disable boymoo-compiler::data-constant boymoo-compiler::read-lines
                                      boymoo-compiler::data-datum a-spelled-source-symbol-selects-its-home-name-reader
                                      mv-nth))))
