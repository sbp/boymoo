(in-package "BOYMOO-PROOFS")

(include-book "program-layout")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable data-state-sized-p data-block-sized-p data-state-buckets-p
                     data-storable-table-p mv-nth char length ash
                     boymoo-compiler::data-block boymoo-compiler::data-with-block
                     boymoo-compiler::data-list-cells boymoo-compiler::data-bucket-add
                     boymoo-compiler::data-symbol boymoo-compiler::data-remember
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                     boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::table-get boymoo-compiler::table-put
                     boymoo-compiler::text-hash boymoo-compiler::compiler-error
                     boymoo-compiler::declaration-list data-symbol-storage-input-p)))

(local
 (defthm sized-state-stores-its-name-lookup
   (implies (data-state-sized-p state-data start)
            (and (not (stringp (boymoo-compiler::table-get key hash 12 (car state-data))))
                 (not (stringp (cdr (boymoo-compiler::table-get key hash 12 (car state-data)))))))))

(local
 (defthm data-import-step-preserves-sized-state
   (implies (and (data-state-sized-p state-data start) (not (stringp entry)) (not (stringp (cdr entry)))
                 (not (stringp symbol-ref)))
            (data-state-sized-p
             (boymoo-compiler::data-bucket-add
              number name (cdr entry) symbol-ref
              (cons (boymoo-compiler::table-put (cons number name) (cons :import entry)
                                               (+ (boymoo-compiler::text-hash name) (* 7919 number))
                                               12 (car state-data))
                    (cdr state-data)))
             start))))

(defthm data-imports-preserve-sized-state
  (implies (and (data-formals-storage-input-p imports) (data-state-sized-p state-data start)
                (data-word-chunks-p reversed))
           (and (not (stringp (mv-nth 0 (boymoo-compiler::data-imports
                                         imports number packages common-lisp state-data reversed))))
                (data-state-sized-p (mv-nth 1 (boymoo-compiler::data-imports
                                               imports number packages common-lisp state-data reversed))
                                    start)))
  :hints (("Goal" :induct (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed)
                  :in-theory (disable data-bucket-add-preserves-sized-state))
          ("Subgoal *1/4"
           :use ((:instance data-symbol-preserves-sized-state (text (car imports))))
           :in-theory (disable data-symbol-preserves-sized-state))
          ("Subgoal *1/1"
           :use ((:instance data-list-cells-preserves-sized-block
                            (tail 34) (block (boymoo-compiler::data-block state-data))))
           :in-theory (disable data-list-cells-preserves-sized-block))))

(local
 (in-theory (disable boymoo-compiler::data-imports boymoo-compiler::data-vector
                     boymoo-compiler::data-text boymoo-compiler::data-intern
                     boymoo-compiler::reverse-onto)))

(local
 (defthm vector-word-is-nonstring
   (not (stringp (mv-nth 0 (boymoo-compiler::data-vector fields block))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-vector)))))

(local
 (defthm text-word-is-nonstring
   (not (stringp (mv-nth 0 (boymoo-compiler::data-text type text block))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-text)))))

(local
 (defthm declaration-import-list-is-storable
   (implies (data-storable-table-p declarations 12 :declaration)
            (not (stringp (cadr (boymoo-compiler::index-get name declarations)))))
   :hints (("Goal" :use ((:instance data-index-get-returns-storable-value
                                    (index declarations) (text name) (kind :declaration)))
                   :in-theory (disable data-index-get-returns-storable-value)))))

(defthm data-package-vectors-preserve-sized-state
  (implies (and (string-listp names) (data-state-sized-p state-data start)
                (data-storable-table-p declarations 12 :declaration) (data-word-chunks-p reversed))
           (data-state-sized-p (mv-nth 1 (boymoo-compiler::data-package-vectors
                                          names packages declarations state-data reversed)) start))
  :hints (("Goal" :induct (boymoo-compiler::data-package-vectors names packages declarations state-data reversed))
          ("Subgoal *1/2"
           :use ((:instance data-intern-preserves-sized-state
                            (package (boymoo-compiler::index-get (car names) packages))
                            (name "ACL2-PKG-WITNESS")
                            (state-data (boymoo-compiler::data-with-block
                                         (mv-nth 1 (boymoo-compiler::data-text
                                                    1 (car names) (boymoo-compiler::data-block state-data)))
                                         state-data))))
           :in-theory (disable data-intern-preserves-sized-state))))

(defun data-package-lines-storage-input-p (lines)
  (if (atom lines)
      t
    (let* ((text (cadar lines))
           (imports (caddar lines)))
      (and (stringp (boymoo-compiler::decode-part text 0 (length text)))
           (data-formals-storage-input-p (boymoo-compiler::declaration-list imports))
           (data-package-lines-storage-input-p (cdr lines))))))

(local
 (defthm package-names-reverse-onto-strings
   (implies (and (string-listp names) (string-listp tail))
            (string-listp (boymoo-compiler::reverse-onto names tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto names tail)
                   :in-theory (enable boymoo-compiler::reverse-onto)))))

(defthm data-package-declarations-preserve-sized-state
  (implies (and (data-package-lines-storage-input-p lines) (data-state-sized-p state-data start)
                (data-storable-table-p declarations 12 :declaration) (string-listp names))
           (mv-let (decls next rows)
             (boymoo-compiler::data-package-declarations lines packages declared declarations state-data names)
             (and (data-storable-table-p decls 12 :declaration)
                  (data-state-sized-p next start) (string-listp rows))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-declarations
                            lines packages declared declarations state-data names)
                  :in-theory (disable data-formals-storage-input-p boymoo-compiler::decode-part))))

(defthm data-packages-preserve-sized-state
  (implies (and (data-package-lines-storage-input-p lines) (data-state-sized-p state-data start)
                (data-word-chunks-p reversed))
           (data-state-sized-p (mv-nth 1 (boymoo-compiler::data-packages
                                           lines number packages state-data reversed)) start))
  :hints (("Goal" :use ((:instance data-package-declarations-preserve-sized-state
                                   (declared nil) (declarations nil) (names nil)))
                  :in-theory (disable boymoo-compiler::data-package-declarations
                                      boymoo-compiler::data-package-vectors
                                      data-package-lines-storage-input-p))))

(defthmd data-build-body-is-sized-for-storage-input
  (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                (mv-nth 0 (data-before-buckets lines package-lines)))
           (data-block-sized-p (boymoo-compiler::data-block (mv-nth 2 (data-before-buckets lines package-lines)))
                                80))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-initial boymoo-compiler::data-packages
                                      boymoo-compiler::data-program-symbols boymoo-compiler::data-package-numbers
                                      data-program-storage-input-p data-package-lines-storage-input-p))))

(defthmd data-build-image-has-exact-size-for-storage-input
  (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                (mv-nth 0 (data-before-buckets lines package-lines)))
           (proof-image-p (car (boymoo-compiler::data-build lines package-lines))))
  :hints (("Goal" :use (data-build-count-matches-image-for-sized-body data-build-body-is-sized-for-storage-input)
                  :in-theory (disable boymoo-compiler::data-build data-before-buckets proof-image-p
                                      data-program-storage-input-p data-package-lines-storage-input-p))))

(local
 (defthm quotient-of-eight-times-count
   (equal (* 1/8 (* 8 count)) (fix count))
   :hints (("Goal" :use ((:instance associativity-of-* (acl2::x 1/8) (acl2::y 8) (acl2::z count)))
                   :in-theory (disable associativity-of-*)))))

(local
 (defthm aligned-eight-bytes-counts-whole-words
   (implies (integerp size)
            (integerp (* 1/8 (boymoo-compiler::aligned-size size 3))))
   :hints (("Goal" :use ((:instance data-ash-left (word (ash (+ size 7) -3)) (width 3)))
                   :in-theory (disable ash)))))

(local
 (defthm chunk-counts-whole-words
   (integerp (* 1/8 (data-chunk-size chunk)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::aligned-size)))))

(local
 (defthm chunk-list-counts-whole-words
   (integerp (* 1/8 (data-chunks-size reversed)))
   :hints (("Goal" :induct (data-chunks-size reversed)
                   :in-theory (disable data-chunk-size chunk-counts-whole-words))
           ("Subgoal *1/2" :use ((:instance chunk-counts-whole-words (chunk (car reversed))))))))

(local
 (defthm whole-word-count-is-aligned
   (implies (and (integerp size) (integerp (* 1/8 size)))
            (equal (mod size 8) 0))
   :hints (("Goal" :use ((:instance data-floor-unique (d 8) (q (* 1/8 size)) (x size)))
                   :in-theory (disable floor)))))

(defthmd data-build-declared-size-is-word-aligned
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (header (mv-nth 0 (data-image-parts lines package-lines))))
    (implies (and header (proof-image-p image)) (equal (mod (car image) 8) 0)))
  :hints (("Goal" :use (data-build-fragment-count-agreement
                       (:instance chunk-list-counts-whole-words
                                  (reversed (mv-nth 1 (data-image-parts lines package-lines))))
                       (:instance whole-word-count-is-aligned
                                  (size (car (car (boymoo-compiler::data-build lines package-lines))))))
                  :in-theory (disable boymoo-compiler::data-build data-image-parts
                                      proof-fragments-size proof-fragments-p data-chunks-size mod
                                      whole-word-count-is-aligned chunk-list-counts-whole-words))))
