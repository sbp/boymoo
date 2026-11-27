(in-package "BOYMOO-PROOFS")

(include-book "builder-map")
(include-book "front-agreement")
(include-book "quote-elaboration")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p data-before-buckets
                     data-build-allocation-records data-build-allocation-check-p data-static-image-witness-p
                     data-static-image-map data-static-views-p proof-static-initial-p proof-constant-map-p
                     data-indexable-lines-p data-program-storage-input-p data-program-constant-keys-p
                     data-package-lines-storage-input-p boymoo-compiler::read-program boymoo-compiler::index-lines
                     boymoo-compiler::data-build boymoo-compiler::index-get data-latest-arities proof-index-agrees-p
                     proof-image-p proof-image-at-p mod)))

(defthmd data-checked-text-and-allocations-give-static-agreement
  (let* ((parsed (boymoo-compiler::read-program text))
         (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
         (arities (mv-nth 1 pass)) (package-lines (mv-nth 4 pass))
         (witness (data-build-allocation-records parsed package-lines base)))
    (mv-let (image constants) (boymoo-compiler::data-build parsed package-lines)
      (implies (and (data-program-spans-p text events lines)
                    (data-source-lines-spelled-p lines sources bindings nil nil)
                    (data-quote-spellings-p bindings witnesses) (string-listp queries)
                    (mv-nth 0 (data-before-buckets parsed package-lines))
                    (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                    (equal (mod base 8) 0) (data-build-allocation-check-p parsed package-lines base)
                    (data-static-views-p base witness packages machine)
                    (proof-constant-map-p bindings constants base witness packages machine))
               (mv-let (ok objects) (data-static-image-map base image constants machine)
                 (and ok (proof-static-initial-p base objects packages machine)
                      (proof-constant-map-p bindings constants base objects packages machine)
                      (proof-index-agrees-p (data-latest-arities queries lines) arities))))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        (:instance data-checked-builder-allocations-construct-the-static-witness
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil))))
                        (:instance data-checked-text-and-ranked-witness-give-static-agreement
                                   (witness (data-build-allocation-records
                                             (boymoo-compiler::read-program text)
                                             (mv-nth 4 (boymoo-compiler::index-lines
                                                        (boymoo-compiler::read-program text)
                                                        nil nil nil nil nil nil nil)) base)))))))

(local
 (in-theory (disable data-static-word-present-p data-table-p data-table-bindings proof-constant-word)))

(local
 (defthm present-static-word-is-nonnil
   (implies (data-static-word-present-p word base objects) word)
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-static-word-present-p)))))

(local
 (defthm present-constant-binding-has-a-word
   (implies (and (data-static-constant-words-present-p bindings base objects) (member-equal binding bindings))
            (and (proof-constant-word (cdr binding))
                 (data-static-word-present-p (proof-constant-word (cdr binding)) base objects)))
   :hints (("Goal" :induct (data-static-constant-words-present-p bindings base objects)))))

(defthmd data-successful-scan-gives-a-word-for-each-present-index-entry
  (let* ((entry (boymoo-compiler::index-get query constants)) (word (proof-constant-word entry)))
    (mv-let (ok objects) (data-static-image-map base image constants machine)
      (implies (and ok (data-table-p constants 12) (stringp query) entry)
               (and word (data-static-word-present-p word base objects)))))
  :hints (("Goal" :use (data-static-map-on-success-covers-roots
                        (:instance data-index-lookup-is-an-enumerated-binding (text query) (index constants))
                        (:instance present-constant-binding-has-a-word
                                   (binding (cons query (boymoo-compiler::index-get query constants)))
                                   (bindings (data-table-bindings constants 12))
                                   (objects (mv-nth 1 (data-static-image-map base image constants machine)))))
                  :in-theory (disable present-constant-binding-has-a-word data-static-constant-words-present-p))))

(local
 (defthm checked-constant-spelling-is-text
   (implies (data-constant-spells-value-p query events datum value) (stringp query))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable data-reader-events data-symbol-spelling-p data-delimited-text-p
                                       data-parsed-datum-spells-value-p data-character-text-p
                                       data-rational-text-p data-complex-text-p)))))

(local
 (in-theory (disable data-constant-spells-value-p data-quote-witness-for-text data-program-quote-count
                     boymoo-compiler::data-package-numbers)))

(defthmd data-checked-program-quote-supplies-its-spelling
  (let ((witness (data-quote-witness-for-text query bindings witnesses))
        (binding (assoc-equal query bindings)))
    (implies (and (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-quote-spellings-p bindings witnesses) (< 0 (data-program-quote-count lines query)))
             (and binding (stringp query)
                  (data-constant-spells-value-p query (car witness) (cadr witness) (cdr binding)))))
  :hints (("Goal" :use ((:instance data-related-program-quote-has-source-binding
                                   (text query) (entry nil) (target nil))
                        (:instance data-quote-lookup-has-its-checked-spelling (text query))))))

(defthmd data-checked-text-and-allocations-represent-every-non-symbol-quote
  (let* ((parsed (boymoo-compiler::read-program text))
         (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
         (package-lines (mv-nth 4 pass))
         (value (cdr (assoc-equal query bindings))))
    (mv-let (image constants) (boymoo-compiler::data-build parsed package-lines)
      (implies (and (data-program-spans-p text events lines)
                    (data-source-lines-spelled-p lines sources bindings nil nil)
                    (data-quote-spellings-p bindings witnesses) (< 0 (data-program-quote-count lines query))
                    (not (symbolp value)) (mv-nth 0 (data-before-buckets parsed package-lines))
                    (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                    (equal (mod base 8) 0) (data-build-allocation-check-p parsed package-lines base))
               (mv-let (ok objects) (data-static-image-map base image constants machine)
                 (let* ((entry (boymoo-compiler::index-get query constants)) (word (proof-constant-word entry)))
                   (and ok entry word (data-static-word-present-p word base objects)))))))
  :hints (("Goal" :use (data-checked-program-quote-supplies-its-spelling
                        data-read-program-gives-source-front-pass-inputs
                        (:instance data-build-retains-nil-and-t-index-entries
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil))))
                        (:instance data-checked-text-records-every-spelled-non-symbol-quote
                                   (quote-events (car (data-quote-witness-for-text query bindings witnesses)))
                                   (datum (cadr (data-quote-witness-for-text query bindings witnesses)))
                                   (value (cdr (assoc-equal query bindings))))
                        (:instance data-checked-builder-allocations-scan-successfully
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil))))
                        (:instance data-successful-scan-gives-a-word-for-each-present-index-entry
                                   (image (car (boymoo-compiler::data-build
                                                (boymoo-compiler::read-program text)
                                                (mv-nth 4 (boymoo-compiler::index-lines
                                                           (boymoo-compiler::read-program text)
                                                           nil nil nil nil nil nil nil)))))
                                   (constants (mv-nth 1 (boymoo-compiler::data-build
                                                         (boymoo-compiler::read-program text)
                                                         (mv-nth 4 (boymoo-compiler::index-lines
                                                                    (boymoo-compiler::read-program text)
                                                                    nil nil nil nil nil nil nil))))))
                        (:instance data-build-common-lisp-number-agrees-with-index
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil)))))
                  :in-theory (disable data-constant-binding-texts-p data-quote-witness-for-text
                                      data-package-lines-match-source-p data-table-p data-static-known-records-p))))

(local (in-theory (disable data-elaborate-program-with-quotes)))

(defthmd data-elaborated-text-and-allocations-give-static-agreement
  (mv-let (elaborated events lines sources bindings witnesses) (data-elaborate-program-with-quotes text packages)
    (declare (ignore events sources witnesses))
    (let* ((parsed (boymoo-compiler::read-program text))
           (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
           (arities (mv-nth 1 pass)) (package-lines (mv-nth 4 pass))
           (witness (data-build-allocation-records parsed package-lines base)))
      (mv-let (image constants) (boymoo-compiler::data-build parsed package-lines)
        (implies (and elaborated (string-listp queries) (mv-nth 0 (data-before-buckets parsed package-lines))
                      (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                      (equal (mod base 8) 0) (data-build-allocation-check-p parsed package-lines base)
                      (data-static-views-p base witness packages machine)
                      (proof-constant-map-p bindings constants base witness packages machine))
                 (mv-let (ok objects) (data-static-image-map base image constants machine)
                   (and ok (proof-static-initial-p base objects packages machine)
                        (proof-constant-map-p bindings constants base objects packages machine)
                        (proof-index-agrees-p (data-latest-arities queries lines) arities)))))))
  :hints (("Goal" :use (data-elaborated-program-with-quotes-supplies-all-checked-relations
                        (:instance data-checked-text-and-allocations-give-static-agreement
                                   (events (mv-nth 1 (data-elaborate-program-with-quotes text packages)))
                                   (lines (mv-nth 2 (data-elaborate-program-with-quotes text packages)))
                                   (sources (mv-nth 3 (data-elaborate-program-with-quotes text packages)))
                                   (bindings (mv-nth 4 (data-elaborate-program-with-quotes text packages)))
                                   (witnesses (mv-nth 5 (data-elaborate-program-with-quotes text packages))))))))
