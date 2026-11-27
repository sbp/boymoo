(in-package "BOYMOO-PROOFS")

(include-book "static-block")
(include-book "generator-inputs")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm assembly-static-index-datum-type
   (equal (assembly-generator-value-p value :datum)
          (assembly-static-datum-word-p value))))

(local (in-theory (disable length char ash boymoo-compiler::low-bits
                           boymoo-compiler::text-hash boymoo-compiler::table-get
                           boymoo-compiler::table-put boymoo-compiler::table-tree-get
                           boymoo-compiler::table-tree-put boymoo-compiler::symbol-separator
                           boymoo-compiler::decode-symbol-part boymoo-compiler::decode-part
                           (:executable-counterpart boymoo-compiler::compiler-error)
                           assembly-generator-index-p assembly-generator-tree-p
                           assembly-static-datum-word-p assembly-static-block-p)))

(defthm assembly-static-index-set-preserves-types
  (implies (and (assembly-generator-index-p index 12 kind)
                (assembly-generator-value-p value kind))
           (assembly-generator-index-p (boymoo-compiler::index-set text value index) 12 kind)))

(defthm assembly-static-index-datum-type-of-lookup
  (implies (assembly-generator-index-p index 12 :datum)
           (assembly-static-datum-word-p (boymoo-compiler::index-get text index)))
  :hints (("Goal" :use ((:instance assembly-generator-value-of-index-get
                                   (key text) (hash (boymoo-compiler::text-hash text))
                                   (bits 12) (kind :datum))))))

(defthm assembly-static-index-name-type-of-lookup
  (implies (assembly-generator-index-p index bits :static-name)
           (assembly-generator-value-p (boymoo-compiler::table-get key hash bits index) :static-name))
  :hints (("Goal" :use ((:instance assembly-generator-value-of-index-get (kind :static-name))))))

(defthm assembly-static-index-declaration-type-of-lookup
  (implies (assembly-generator-index-p index 12 :static-declaration)
           (not (stringp (cadr (boymoo-compiler::index-get text index)))))
  :hints (("Goal" :use ((:instance assembly-generator-value-of-index-get
                                   (key text) (hash (boymoo-compiler::text-hash text))
                                   (bits 12) (kind :static-declaration))))))

(local (in-theory (disable boymoo-compiler::index-set boymoo-compiler::index-get)))

(local
 (defthm assembly-first-symbol-collection-result
   (equal (mv-nth 0 values) (car values))))

(local
 (defthm assembly-second-symbol-collection-result
   (equal (mv-nth 1 values) (cadr values))))

(local
 (defthm assembly-third-symbol-collection-result
   (equal (mv-nth 2 values) (caddr values))))

(defun assembly-static-bucket-tree-p (tree bits)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) t)
        ((zp bits) (not (stringp (car tree))))
        (t (and (assembly-static-bucket-tree-p (car tree) (1- bits))
                (assembly-static-bucket-tree-p (cdr tree) (1- bits))))))

(local
 (defthm assembly-static-bucket-branches
   (implies (assembly-static-bucket-tree-p tree bits)
            (and (implies (zp bits) (not (stringp (car tree))))
                 (implies (not (zp bits))
                          (and (assembly-static-bucket-tree-p (car tree) (1- bits))
                               (assembly-static-bucket-tree-p (cdr tree) (1- bits))))))))

(local
 (defthm assembly-static-bucket-get-is-word
   (implies (assembly-static-bucket-tree-p tree bits)
            (not (stringp (boymoo-compiler::bucket-get bucket bits tree))))
   :hints (("Goal" :induct (boymoo-compiler::bucket-get bucket bits tree)))))

(local
 (defthm assembly-static-bucket-put-preserves-type
   (implies (and (assembly-static-bucket-tree-p tree bits) (not (stringp word)))
            (assembly-static-bucket-tree-p (boymoo-compiler::bucket-set bucket bits word tree) bits))
   :hints (("Goal" :induct (boymoo-compiler::bucket-set bucket bits word tree)))))

(defthm assembly-static-bucket-vector-size
  (implies (and (assembly-static-bucket-tree-p tree bits) (assembly-static-block-p block))
           (assembly-static-block-p (boymoo-compiler::data-bucket-vector tree bits block)))
  :hints (("Goal" :induct (boymoo-compiler::data-bucket-vector tree bits block)
                  :in-theory (disable boymoo-compiler::data-word))))

(defun assembly-static-data-state-p (state-data)
  (and (assembly-generator-index-p (car state-data) 12 :static-name)
       (assembly-generator-index-p (cadr state-data) 12 :datum)
       (assembly-static-bucket-tree-p (caddr state-data) 12)
       (assembly-static-block-p (boymoo-compiler::data-block state-data))))

(local
 (defthm assembly-static-state-from-components
   (implies (and (assembly-generator-index-p names 12 :static-name)
                 (assembly-generator-index-p constants 12 :datum)
                 (assembly-static-bucket-tree-p buckets 12)
                 (assembly-static-block-p block))
            (assembly-static-data-state-p (list* names constants buckets block)))))

(defthm assembly-static-state-uses-typed-constants
  (implies (assembly-static-data-state-p state-data)
           (assembly-constant-index-p (cadr state-data) 12)))

(local
 (defthm assembly-static-state-has-typed-names
   (implies (assembly-static-data-state-p state-data)
            (assembly-generator-index-p (car state-data) 12 :static-name))))

(defthm assembly-static-state-has-sized-block
  (implies (assembly-static-data-state-p state-data)
           (assembly-static-block-p (boymoo-compiler::data-block state-data))))

(defthm assembly-static-state-has-typed-buckets
  (implies (assembly-static-data-state-p state-data)
           (assembly-static-bucket-tree-p (caddr state-data) 12)))

(defthm assembly-static-state-with-data-block
  (implies (and (assembly-static-data-state-p state-data) (assembly-static-block-p block))
           (assembly-static-data-state-p (boymoo-compiler::data-with-block block state-data))))

(defthm assembly-static-state-remembers-typed-datum
  (implies (and (assembly-static-data-state-p state-data) (assembly-static-datum-word-p datum))
           (assembly-static-data-state-p (boymoo-compiler::data-remember text datum state-data))))

(local (in-theory (disable boymoo-compiler::data-word boymoo-compiler::data-text
                           boymoo-compiler::data-cell boymoo-compiler::data-fields
                           boymoo-compiler::bucket-get boymoo-compiler::bucket-set
                           boymoo-compiler::data-remember boymoo-compiler::data-with-block
                           assembly-static-bucket-tree-p)))

(local
 (defthm assembly-static-state-adds-bucket-entry
   (implies (and (assembly-static-data-state-p state-data)
                 (not (stringp name-ref)) (not (stringp symbol-ref)))
            (assembly-static-data-state-p
             (boymoo-compiler::data-bucket-add package name name-ref symbol-ref state-data)))))

(local
 (defthm assembly-static-state-inserts-owned-name
   (implies (and (assembly-static-data-state-p state-data)
                 (assembly-static-block-p block)
                 (integerp symbol-ref)
                 (not (stringp name-ref)))
            (assembly-static-data-state-p
             (list* (boymoo-compiler::table-put key (cons symbol-ref name-ref) hash 12
                                               (car state-data))
                    (cadr state-data) (caddr state-data) block)))))

(local (in-theory (disable boymoo-compiler::data-bucket-add)))

(defthm assembly-static-state-interns-name
  (let ((out (boymoo-compiler::data-intern package name state-data)))
    (implies (and (assembly-static-data-state-p state-data) (stringp name))
             (and (assembly-static-datum-word-p (car out))
                  (not (stringp (cadr out)))
                  (assembly-static-data-state-p (caddr out)))))
  :hints (("Goal"
           :use ((:instance assembly-static-index-name-type-of-lookup
                            (key (cons package name))
                            (hash (+ (boymoo-compiler::text-hash name) (* 7919 package)))
                            (bits 12) (index (car state-data))))
           :in-theory (disable assembly-static-index-name-type-of-lookup))))

(defun assembly-static-symbol-input-p (text)
  (let ((split (boymoo-compiler::symbol-separator text)))
    (and (stringp text) split
         (stringp (boymoo-compiler::decode-symbol-part text (+ split 2) (length text))))))

(local (in-theory (disable boymoo-compiler::data-intern)))

(defthm assembly-static-state-collects-symbol
  (let ((out (boymoo-compiler::data-symbol text packages state-data)))
    (implies (and (assembly-static-data-state-p state-data)
                  (assembly-static-symbol-input-p text))
             (and (assembly-static-datum-word-p (car out))
                  (assembly-static-data-state-p (cadr out))))))

(local (in-theory (disable boymoo-compiler::data-symbol assembly-static-symbol-input-p)))

(defthm assembly-static-state-notes-symbol
  (implies (and (assembly-static-data-state-p state-data) (assembly-static-symbol-input-p text))
           (assembly-static-data-state-p (boymoo-compiler::data-note-symbol text packages state-data))))

(defun assembly-static-symbol-list-p (texts)
  (if (atom texts)
      t
    (and (assembly-static-symbol-input-p (car texts))
         (assembly-static-symbol-list-p (cdr texts)))))

(local (in-theory (disable boymoo-compiler::data-note-symbol assembly-static-data-state-p)))

(defthm assembly-static-state-collects-formals
  (implies (and (assembly-static-data-state-p state-data) (assembly-static-symbol-list-p formals))
           (assembly-static-data-state-p (boymoo-compiler::data-formals formals packages state-data))))

(local
 (defthm assembly-static-index-name-is-word-of-lookup
   (implies (assembly-generator-index-p index bits :static-name)
            (and (not (stringp (boymoo-compiler::table-get key hash bits index)))
                 (not (stringp (cdr (boymoo-compiler::table-get key hash bits index))))))
   :hints (("Goal" :use (assembly-static-index-name-type-of-lookup)
                   :in-theory (disable assembly-static-index-name-type-of-lookup)))))

(local
 (defthm assembly-static-state-inserts-imported-name
   (implies (and (assembly-static-data-state-p state-data)
                 (not (stringp entry)))
            (assembly-static-data-state-p
             (cons (boymoo-compiler::table-put key (cons :import entry) hash 12 (car state-data))
                   (cdr state-data))))
   :hints (("Goal" :in-theory (enable assembly-static-data-state-p)))))

(local
 (defthm assembly-static-state-imports-name
   (implies (and (assembly-static-data-state-p state-data)
                 (not (stringp entry))
                 (not (stringp (cdr entry)))
                 (assembly-static-datum-word-p symbol-ref))
            (assembly-static-data-state-p
             (boymoo-compiler::data-bucket-add
              number name (cdr entry) symbol-ref
              (cons (boymoo-compiler::table-put key (cons :import entry) hash 12 (car state-data))
                    (cdr state-data)))))))

(local
 (defthm assembly-static-words-of-cons
   (equal (assembly-static-words-p (cons word rest))
          (and (not (stringp word)) (assembly-static-words-p rest)))))

(local (in-theory (disable boymoo-compiler::data-block)))

(defthm assembly-static-state-collects-imports
  (let ((out (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed)))
    (implies (and (assembly-static-data-state-p state-data)
                  (assembly-static-symbol-list-p imports)
                  (assembly-static-words-p reversed))
             (and (assembly-static-datum-word-p (car out))
                  (assembly-static-data-state-p (cadr out)))))
  :hints (("Goal"
           :induct (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed)
           :in-theory (disable assembly-static-words-p boymoo-compiler::data-list-cells))))

(defthm assembly-static-initial-state-is-sized
  (let ((out (boymoo-compiler::data-initial package)))
    (and (integerp (car out)) (integerp (cadr out))
         (assembly-static-data-state-p (caddr out))))
  :hints (("Goal" :in-theory (disable (:executable-counterpart boymoo-compiler::data-text)
                                      (:executable-counterpart boymoo-compiler::index-set)))))
