(in-package "BOYMOO-PROOFS")

(include-book "builder")

(logic)
(set-verify-guards-eagerness 0)

; A reference occupies a word chunk. In particular, no index lookup
; used as a reference can be mistaken for a string chunk.
(defun data-storable-table-value-p (kind value)
  (and (not (stringp value))
       (case kind
         (:name (and (not (stringp (car value))) (not (stringp (cdr value)))))
         (:declaration (not (stringp (cadr value))))
         (otherwise t))))

(defun data-storable-tree-p (tree kind)
  (if (atom tree)
      t
    (and (data-storable-table-value-p kind (cddar tree))
         (data-storable-tree-p (cadr tree) kind)
         (data-storable-tree-p (cddr tree) kind))))

(defun data-storable-table-p (tree bits kind)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) t)
        ((zp bits) (data-storable-tree-p tree kind))
        (t (and (data-storable-table-p (car tree) (1- bits) kind)
                (data-storable-table-p (cdr tree) (1- bits) kind)))))

(local
 (defthm empty-tree-has-storable-values
   (implies (atom tree) (data-storable-tree-p tree kind))))

(defthm data-empty-table-has-storable-values
  (data-storable-table-p nil bits kind))

(local
 (defthm storable-tree-fields
   (implies (data-storable-tree-p tree kind)
            (and (data-storable-table-value-p kind (cddar tree))
                 (data-storable-tree-p (cadr tree) kind)
                 (data-storable-tree-p (cddr tree) kind)))))

(local
 (defthm storable-tree-of-table-node
   (equal (data-storable-tree-p (boymoo-compiler::table-node entry left right) kind)
          (and (data-storable-table-value-p kind (cdr entry))
               (data-storable-tree-p left kind)
               (data-storable-tree-p right kind)))))

(local
 (defthm storable-tree-after-balance
   (implies (and (data-storable-table-value-p kind (cdr entry))
                 (data-storable-tree-p left kind) (data-storable-tree-p right kind))
            (data-storable-tree-p (boymoo-compiler::table-balance entry left right) kind))
   :hints (("Goal" :in-theory (disable boymoo-compiler::table-node boymoo-compiler::table-height
                                       data-storable-tree-p data-storable-table-value-p)))))

(local
 (defthm table-tree-get-returns-storable-value
   (implies (data-storable-tree-p tree kind)
            (data-storable-table-value-p kind (boymoo-compiler::table-tree-get key tree)))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-get key tree)))))

(local
 (defthm table-tree-put-preserves-storable-values
   (implies (and (data-storable-tree-p tree kind) (data-storable-table-value-p kind value))
            (data-storable-tree-p (boymoo-compiler::table-tree-put key value tree) kind))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-put key value tree)
                   :in-theory (disable boymoo-compiler::table-node boymoo-compiler::table-balance
                                       data-storable-tree-p data-storable-table-value-p)))))

(local
 (in-theory (disable boymoo-compiler::low-bits ash boymoo-compiler::text-hash
                     boymoo-compiler::table-tree-get boymoo-compiler::table-tree-put)))

(defthm data-table-get-returns-storable-value
  (implies (data-storable-table-p tree bits kind)
           (data-storable-table-value-p kind (boymoo-compiler::table-get key hash bits tree)))
  :hints (("Goal" :induct (boymoo-compiler::table-get key hash bits tree))))

(defthm data-table-put-preserves-storable-values
  (implies (and (data-storable-table-p tree bits kind) (data-storable-table-value-p kind value))
           (data-storable-table-p (boymoo-compiler::table-put key value hash bits tree) bits kind))
  :hints (("Goal" :induct (boymoo-compiler::table-put key value hash bits tree)
                  :in-theory (disable data-storable-tree-p data-storable-table-value-p))))

(local (in-theory (disable boymoo-compiler::table-get boymoo-compiler::table-put)))

(defthm data-index-get-returns-storable-value
  (implies (data-storable-table-p index 12 kind)
           (data-storable-table-value-p kind (boymoo-compiler::index-get text index)))
  :hints (("Goal" :in-theory (disable data-storable-table-p data-storable-table-value-p))))

(defthm data-index-set-preserves-storable-values
  (implies (and (data-storable-table-p index 12 kind) (data-storable-table-value-p kind value))
           (data-storable-table-p (boymoo-compiler::index-set text value index) 12 kind))
  :hints (("Goal" :in-theory (disable data-storable-table-p data-storable-table-value-p))))

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set data-storable-table-p)))

(defun data-state-sized-p (state-data start)
  (and (data-block-sized-p (boymoo-compiler::data-block state-data) start)
       (data-state-buckets-p state-data)
       (data-storable-table-p (car state-data) 12 :name)
       (data-storable-table-p (cadr state-data) 12 :constant)))

(defthm data-sized-state-has-sized-block
  (implies (data-state-sized-p state-data start)
           (data-block-sized-p (boymoo-compiler::data-block state-data) start)))

(defthm data-sized-state-storage-components
  (implies (data-state-sized-p state-data start)
           (and (data-storable-table-p (car state-data) 12 :name)
                (data-storable-table-p (cadr state-data) 12 :constant)
                (data-state-buckets-p state-data)))
  :rule-classes :forward-chaining)

(defthm data-block-replacement-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (data-block-sized-p block start))
           (data-state-sized-p (boymoo-compiler::data-with-block block state-data) start)))

(defthm data-remember-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (not (stringp datum)))
           (data-state-sized-p (boymoo-compiler::data-remember text datum state-data) start))
  :hints (("Goal" :in-theory (enable data-index-set-preserves-storable-values))))

(local
 (defthm bucket-head-is-storable
   (implies (data-static-bucket-tree-p tree bits)
            (not (stringp (boymoo-compiler::bucket-get bucket bits tree))))
   :hints (("Goal" :induct (boymoo-compiler::bucket-get bucket bits tree)))))

(local
 (defthm sized-state-has-storable-bucket-head
   (implies (data-state-buckets-p state-data)
            (not (stringp (boymoo-compiler::bucket-get bucket 12 (caddr state-data)))))
   :hints (("Goal" :use ((:instance bucket-head-is-storable (bits 12) (tree (caddr state-data))))
                   :in-theory (disable boymoo-compiler::bucket-get bucket-head-is-storable)))))

(local
 (defthm sized-offset-is-a-word
   (implies (data-block-sized-p block start) (not (stringp (car block))))
   :hints (("Goal" :in-theory (enable data-block-sized-p)))))

(local
 (defthm data-cell-word-is-offset
   (equal (mv-nth 0 (boymoo-compiler::data-cell first second block)) (car block))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-cell)))))

(local
 (defthm allocated-cell-end-is-a-word
   (not (stringp (car (mv-nth 1 (boymoo-compiler::data-cell first second block)))))))

(defthm data-bucket-add-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (not (stringp name-ref)) (not (stringp symbol-ref)))
           (data-state-sized-p (boymoo-compiler::data-bucket-add package name name-ref symbol-ref state-data)
                               start))
  :hints (("Goal" :use (data-bucket-add-preserves-bucket-tree)
                  :in-theory (disable boymoo-compiler::data-cell boymoo-compiler::data-word
                                      boymoo-compiler::bucket-get boymoo-compiler::bucket-set
                                      data-state-buckets-p data-bucket-add-preserves-bucket-tree
                                      data-block-sized-p))))

(defthm data-name-table-get-components-are-storable
  (let ((value (boymoo-compiler::table-get key hash 12 table)))
    (implies (data-storable-table-p table 12 :name)
             (and (not (stringp value)) (not (stringp (car value))) (not (stringp (cdr value))))))
  :hints (("Goal" :use ((:instance data-table-get-returns-storable-value
                                   (tree table) (bits 12) (kind :name)))
                  :in-theory (disable data-table-get-returns-storable-value))))

(local
 (defthm constant-memo-is-storable
   (implies (data-storable-table-p constants 12 :constant)
            (not (stringp (boymoo-compiler::index-get text constants))))
   :hints (("Goal" :use ((:instance data-index-get-returns-storable-value
                                    (index constants) (kind :constant)))
                   :in-theory (disable data-index-get-returns-storable-value)))))

(local
 (defthm memo-with-new-name-and-block
   (implies (and (data-state-sized-p state-data start) (data-block-sized-p block start)
                 (data-storable-table-p names 12 :name))
            (data-state-sized-p (list* names (cadr state-data) (caddr state-data) block) start))
   :hints (("Goal" :in-theory (disable data-static-bucket-tree-p data-block-sized-p)))))

(defthm data-name-table-replacement-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (data-storable-table-p names 12 :name))
           (data-state-sized-p (cons names (cdr state-data)) start))
  :hints (("Goal" :in-theory (disable data-static-bucket-tree-p data-block-sized-p))))

(local
 (in-theory (disable data-state-sized-p data-block-sized-p
                     boymoo-compiler::data-block
                     boymoo-compiler::data-bucket-add boymoo-compiler::data-with-block
                     boymoo-compiler::data-remember boymoo-compiler::data-text
                     boymoo-compiler::data-fields boymoo-compiler::data-cell
                     boymoo-compiler::compiler-error)))

(local
 (defthm reference-address-from-text-is-not-a-string
   (not (stringp (mv-nth 0 (boymoo-compiler::data-text type text block))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-text)))))

(local
 (defthm reference-address-from-two-fields-is-not-a-string
   (not (stringp (mv-nth 0 (boymoo-compiler::data-fields type first second block))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-fields)))))

(defthm data-compiler-error-logical-value
  (equal (boymoo-compiler::compiler-error message value) nil)
  :hints (("Goal" :in-theory (enable boymoo-compiler::compiler-error))))

(defthm data-mv-nth-of-cons-at-zero
  (equal (mv-nth 0 (cons first rest)) first))

(defthm data-mv-nth-of-cons-at-positive-index
  (implies (posp index)
           (equal (mv-nth index (cons first rest)) (mv-nth (1- index) rest))))

(local (in-theory (disable mv-nth)))

(defthm data-intern-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (stringp name))
           (and (not (stringp (mv-nth 0 (boymoo-compiler::data-intern package name state-data))))
                (not (stringp (mv-nth 1 (boymoo-compiler::data-intern package name state-data))))
                (data-state-sized-p (mv-nth 2 (boymoo-compiler::data-intern package name state-data)) start)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::table-key-less))))

; A decoded name occupies a string chunk. Lookups of names with no
; separator or no package can return an error without allocating it.
(defun data-symbol-storage-input-p (text)
  (let ((split (boymoo-compiler::symbol-separator text)))
    (or (not (stringp text)) (equal (char text 0) #\") (equal (char text 0) #\#)
        (not split)
        (stringp (boymoo-compiler::decode-symbol-part text (+ 2 split) (length text))))))

(local
 (in-theory (disable boymoo-compiler::data-intern boymoo-compiler::symbol-separator
                     boymoo-compiler::decode-symbol-part char length)))

(defthm data-symbol-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (data-symbol-storage-input-p text))
           (and (not (stringp (mv-nth 0 (boymoo-compiler::data-symbol text packages state-data))))
                (data-state-sized-p (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data)) start))))

(local
 (defthm integer-limbs-are-word-chunks
   (implies (and (not (stringp magnitude)) (data-word-chunks-p tail))
            (data-word-chunks-p (boymoo-compiler::data-integer-limbs magnitude width leading fuel tail)))
   :hints (("Goal" :induct (boymoo-compiler::data-integer-limbs magnitude width leading fuel tail)))))

(local
 (defthm decimal-scanner-does-not-return-a-string
   (implies (not (stringp accumulator))
            (not (stringp (boymoo-compiler::decimal-value text start count accumulator))))
   :hints (("Goal" :induct (boymoo-compiler::decimal-value text start count accumulator)))))

(local
 (defthm integer-reader-does-not-return-a-string
   (not (stringp (boymoo-compiler::data-integer-value text start end)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::decimal-value)))))

(local
 (defthm integer-writer-reference-is-storable
   (not (stringp (mv-nth 0 (boymoo-compiler::data-write-integer value text-length block))))))

(defthm data-write-integer-preserves-sized-block
  (implies (and (data-block-sized-p block start) (not (stringp value)))
           (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-write-integer value text-length block)) start))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-word boymoo-compiler::data-words
                                      boymoo-compiler::data-integer-limbs))))

(local
 (in-theory (disable boymoo-compiler::data-write-integer boymoo-compiler::data-integer-value
                     boymoo-compiler::find-char subseq)))

(defthm data-rational-preserves-sized-block
  (and (not (stringp (mv-nth 0 (boymoo-compiler::data-rational text block))))
       (implies (data-block-sized-p block start)
                (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-rational text block)) start))))

(local (in-theory (disable boymoo-compiler::data-rational)))

(defthm data-number-preserves-sized-block
  (and (not (stringp (mv-nth 0 (boymoo-compiler::data-number text block))))
       (implies (data-block-sized-p block start)
                (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-number text block)) start))))

(defun data-atom-storage-input-p (text)
  (if (equal (char text 0) #\")
      (stringp (boymoo-compiler::decode-part text 0 (length text)))
    (data-symbol-storage-input-p text)))

(local
 (in-theory (disable boymoo-compiler::data-symbol boymoo-compiler::data-number
                     boymoo-compiler::hex-byte boymoo-compiler::decode-part data-symbol-storage-input-p)))

(defthm data-atom-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (data-atom-storage-input-p text))
           (and (not (stringp (mv-nth 0 (boymoo-compiler::data-atom text packages state-data))))
                (data-state-sized-p (mv-nth 1 (boymoo-compiler::data-atom text packages state-data)) start))))

(defthm data-list-cells-preserves-sized-block
  (implies (and (data-block-sized-p block start) (data-word-chunks-p reversed) (not (stringp tail)))
           (and (not (stringp (mv-nth 0 (boymoo-compiler::data-list-cells reversed tail block))))
                (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-list-cells reversed tail block)) start)))
  :hints (("Goal" :induct (boymoo-compiler::data-list-cells reversed tail block))))

(local
 (defthm state-with-empty-buckets-is-sized
   (implies (and (data-block-sized-p block start)
                 (data-storable-table-p names 12 :name)
                 (data-storable-table-p constants 12 :constant))
            (data-state-sized-p (list* names constants nil block) start))
   :hints (("Goal" :in-theory (enable data-state-sized-p data-state-buckets-p
                                      boymoo-compiler::data-block)))))

(local
 (defthm initial-allocation-start
   (data-block-sized-p (cons 80 nil) 80)
   :hints (("Goal" :in-theory (enable data-block-sized-p)))))

(defthm data-initial-state-is-sized
  (data-state-sized-p (mv-nth 2 (boymoo-compiler::data-initial package)) 80)
  :hints (("Goal" :in-theory (disable (:executable-counterpart boymoo-compiler::data-text)
                                      (:executable-counterpart boymoo-compiler::index-set)))))
