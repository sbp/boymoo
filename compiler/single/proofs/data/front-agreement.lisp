(in-package "BOYMOO-PROOFS")

(include-book "package-agreement")
(include-book "quote-presence")
(include-book "static-bounds")
(include-book "static-agreement")

(logic)
(set-verify-guards-eagerness 0)

(defthm data-build-common-lisp-number-agrees-with-index
  (equal (mv-nth 0 (data-before-buckets lines package-lines))
         (boymoo-compiler::index-get
          "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable boymoo-compiler::index-get boymoo-compiler::data-package-numbers
                                      boymoo-compiler::data-initial boymoo-compiler::data-packages
                                      boymoo-compiler::data-program-symbols))))

(local
 (defthm admissible-lines-build-a-sized-image-with-initial-constants
   (implies (and (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                 (data-package-lines-storage-input-p package-lines)
                 (mv-nth 0 (data-before-buckets lines package-lines)))
            (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
              (and (proof-image-p image) (<= 32856 (car image)) (equal (mod (car image) 8) 0)
                   (data-table-p constants 12)
                   (equal (boymoo-compiler::index-get boymoo-compiler::*nil-name* constants) *proof-nil*)
                   (equal (boymoo-compiler::index-get "COMMON-LISP::T" constants) *proof-t*))))
   :rule-classes nil
   :hints (("Goal" :use (data-build-common-lisp-number-agrees-with-index
                         data-build-body-is-sized-for-storage-input data-build-size-includes-the-bucket-vector
                         data-build-image-has-exact-size-for-storage-input data-build-declared-size-is-word-aligned
                         data-build-retains-nil-and-t-index-entries)
                   :in-theory (disable data-before-buckets data-image-parts boymoo-compiler::data-build
                                       boymoo-compiler::index-get boymoo-compiler::data-package-numbers
                                       data-block-sized-p data-program-storage-input-p data-program-constant-keys-p
                                       data-package-lines-storage-input-p proof-image-p mod)))))

(defthmd data-checked-source-text-gives-index-and-sized-image
  (implies (and (data-program-spans-p text events lines)
                (data-source-lines-spelled-p lines sources bindings nil nil)
                (data-quote-spellings-p bindings witnesses) (string-listp queries))
           (let* ((parsed (boymoo-compiler::read-program text))
                  (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
                  (arities (mv-nth 1 pass)) (package-lines (mv-nth 4 pass)))
             (and (equal parsed lines)
                  (proof-index-agrees-p (data-latest-arities queries lines) arities)
                  (data-package-lines-match-source-p
                   package-lines (boymoo-compiler::reverse-onto (data-source-package-lines sources) nil))
                  (implies (mv-nth 0 (data-before-buckets lines package-lines))
                           (mv-let (image constants) (boymoo-compiler::data-build parsed package-lines)
                             (and (proof-image-p image) (<= 32856 (car image))
                                  (equal (mod (car image) 8) 0) (data-table-p constants 12)
                                  (equal (boymoo-compiler::index-get boymoo-compiler::*nil-name* constants) *proof-nil*)
                                  (equal (boymoo-compiler::index-get "COMMON-LISP::T" constants) *proof-t*)))))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        data-index-package-lines-match-source-in-file-order data-index-lines-arity-agreement
                        (:instance admissible-lines-build-a-sized-image-with-initial-constants
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            lines nil nil nil nil nil nil nil)))))
                  :in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines
                                      boymoo-compiler::data-build boymoo-compiler::index-get
                                      boymoo-compiler::reverse-onto data-indexable-lines-p
                                      data-before-buckets data-program-spans-p data-source-lines-spelled-p
                                      data-quote-spellings-p data-latest-arities data-program-constant-keys-p
                                      data-source-package-lines data-package-lines-match-source-p
                                      data-program-storage-input-p data-package-lines-storage-input-p proof-image-p
                                      data-table-p proof-index-agrees-p mod))))

(defthmd data-checked-text-records-every-spelled-non-symbol-quote
  (let* ((parsed (boymoo-compiler::read-program text))
         (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
         (package-lines (mv-nth 4 pass)))
    (implies (and (data-program-spans-p text events lines)
                  (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-quote-spellings-p bindings witnesses)
                  (data-constant-spells-value-p query quote-events datum value) (not (symbolp value))
                  (boymoo-compiler::index-get
                   "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil))
                  (< 0 (data-program-quote-count lines query)))
             (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build parsed package-lines)))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        (:instance data-build-records-every-spelled-non-symbol-quote
                                   (events quote-events) (parsed-datum datum)
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            lines nil nil nil nil nil nil nil)))))
                  :in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines
                                      boymoo-compiler::data-build boymoo-compiler::index-get
                                      boymoo-compiler::data-package-numbers data-program-quote-count
                                      data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p
                                      data-constant-spells-value-p data-indexable-lines-p
                                      data-program-storage-input-p data-program-constant-keys-p
                                      data-package-lines-storage-input-p))))

(defun data-latest-entry-text (lines)
  (if (atom lines)
      nil
    (if (equal (caar lines) "entry") (cadar lines) (data-latest-entry-text (cdr lines)))))

(defun data-source-entry-line (sources)
  (if (atom sources)
      nil
    (if (eq (caar sources) :entry) (car sources) (data-source-entry-line (cdr sources)))))

(defthmd data-index-lines-selects-entry-and-target
  (implies (data-indexable-lines-p lines entry target)
           (mv-let (out-defs out-arities out-attachments out-sources out-packages out-entry out-target)
             (boymoo-compiler::index-lines lines defs arities attachments sources packages entry target)
             (declare (ignore out-defs out-arities out-attachments out-sources out-packages))
             (and (equal out-entry (or entry (data-latest-entry-text lines)))
                  (equal out-target (or target (and (member-equal '("target" "linux") lines) :linux))))))
  :hints (("Goal" :induct (boymoo-compiler::index-lines lines defs arities attachments sources packages entry target)
                  :in-theory (disable boymoo-compiler::index-definitions boymoo-compiler::index-get
                                      boymoo-compiler::index-set boymoo-compiler::reverse-onto
                                      data-indexable-definitions-p data-protected-name-p))))

(local
 (defthm empty-entry-is-not-a-source-spelling
   (not (data-source-symbol-agrees-p nil symbol))))

(local
 (defthm spelled-entry-line-gives-the-source-name
   (let ((entry-text (data-latest-entry-text lines)) (source-line (data-source-entry-line sources)))
     (implies (data-source-lines-spelled-p lines sources bindings entry target)
              (and (iff entry-text source-line)
                   (implies source-line (data-source-symbol-agrees-p entry-text (cadr source-line))))))
   :rule-classes nil
   :hints (("Goal" :induct (data-source-lines-spelled-p lines sources bindings entry target)
                   :in-theory (disable data-source-symbol-agrees-p data-source-symbols-agree-p
                                       data-atom-spells-value-p data-parsed-datum-spells-value-p
                                       data-source-definitions-spelled-p data-protected-name-p)))))

(defthmd data-checked-text-selects-source-entry
  (implies (and (data-program-spans-p text events lines)
                (data-source-lines-spelled-p lines sources bindings nil nil)
                (data-quote-spellings-p bindings witnesses))
           (let* ((parsed (boymoo-compiler::read-program text))
                  (entry (mv-nth 5 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
                  (source-line (data-source-entry-line sources)))
             (and (iff entry source-line)
                  (implies source-line (data-source-symbol-agrees-p entry (cadr source-line))))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        (:instance spelled-entry-line-gives-the-source-name (entry nil) (target nil))
                        (:instance data-index-lines-selects-entry-and-target
                                   (defs nil) (arities nil) (attachments nil) (sources nil)
                                   (packages nil) (entry nil) (target nil)))
                  :in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines
                                      data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p
                                      data-indexable-lines-p data-program-storage-input-p data-program-constant-keys-p
                                      data-package-lines-storage-input-p data-source-entry-line
                                      data-source-symbol-agrees-p data-latest-entry-text))))

(local
 (defthm checked-constant-spellings-have-text-keys
   (implies (data-quote-spellings-p bindings witnesses) (data-constant-binding-texts-p bindings))
   :hints (("Goal" :induct (data-quote-spellings-p bindings witnesses)
                   :in-theory (disable data-reader-events data-parsed-datum-spells-value-p
                                       data-symbol-spelling-p data-delimited-text-p data-character-text-p
                                       data-rational-text-p data-rational-text-value data-complex-text-p
                                       boymoo-compiler::symbol-separator boymoo-compiler::find-char subseq)))))

(defthmd data-checked-text-and-ranked-witness-give-static-agreement
  (let* ((parsed (boymoo-compiler::read-program text))
         (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
         (arities (mv-nth 1 pass)) (package-lines (mv-nth 4 pass)))
    (mv-let (image constants) (boymoo-compiler::data-build parsed package-lines)
      (implies (and (data-program-spans-p text events lines)
                    (data-source-lines-spelled-p lines sources bindings nil nil)
                    (data-quote-spellings-p bindings witnesses) (string-listp queries)
                    (mv-nth 0 (data-before-buckets parsed package-lines))
                    (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                    (equal (mod base 8) 0)
                    (data-static-image-witness-p base image constants machine witness)
                    (data-static-views-p base witness packages machine)
                    (proof-constant-map-p bindings constants base witness packages machine))
               (mv-let (ok objects) (data-static-image-map base image constants machine)
                 (and ok (proof-static-initial-p base objects packages machine)
                      (proof-constant-map-p bindings constants base objects packages machine)
                      (proof-index-agrees-p (data-latest-arities queries lines) arities))))))
  :hints (("Goal" :use (data-checked-source-text-gives-index-and-sized-image
                        (:instance data-build-initial-static-from-placed-witness
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil))))
                        (:instance data-image-scan-preserves-witness-constant-map
                                   (image (car (boymoo-compiler::data-build
                                                (boymoo-compiler::read-program text)
                                                (mv-nth 4 (boymoo-compiler::index-lines
                                                           (boymoo-compiler::read-program text)
                                                           nil nil nil nil nil nil nil)))))
                                   (index (mv-nth 1 (boymoo-compiler::data-build
                                                     (boymoo-compiler::read-program text)
                                                     (mv-nth 4 (boymoo-compiler::index-lines
                                                                (boymoo-compiler::read-program text)
                                                                nil nil nil nil nil nil nil)))))))
                  :in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines
                                      boymoo-compiler::data-build boymoo-compiler::index-get
                                      data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p
                                      data-latest-arities data-table-p data-before-buckets
                                      data-static-image-map data-static-image-witness-p data-static-views-p
                                      data-package-lines-match-source-p proof-constant-map-p proof-index-agrees-p
                                      proof-image-p proof-image-at-p proof-static-initial-p mod))))
