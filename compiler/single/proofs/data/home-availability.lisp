(in-package "BOYMOO-PROOFS")

(include-book "symbol-emission")
(include-book "packages")

(logic)
(set-verify-guards-eagerness 0)

; A package index stores natural numbers even when a lookup is made
; with a token that does not decode to a package name.
(defun data-natural-tree-values-p (tree)
  (or (atom tree)
      (and (or (null (cddar tree)) (natp (cddar tree)))
           (data-natural-tree-values-p (cadr tree))
           (data-natural-tree-values-p (cddr tree)))))

(defun data-natural-table-values-p (tree bits)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) t)
        ((zp bits) (data-natural-tree-values-p tree))
        (t (and (data-natural-table-values-p (car tree) (1- bits))
                (data-natural-table-values-p (cdr tree) (1- bits))))))

(local
 (defthm a-tree-node-has-natural-values
   (equal (data-natural-tree-values-p (boymoo-compiler::table-node entry left right))
          (and (or (not (cdr entry)) (natp (cdr entry)))
               (data-natural-tree-values-p left) (data-natural-tree-values-p right)))))

(local
 (defthm natural-values-in-the-child-trees
   (implies (data-natural-tree-values-p tree)
            (and (or (not (cddar tree)) (natp (cddar tree)))
                 (data-natural-tree-values-p (cadr tree))
                 (data-natural-tree-values-p (cddr tree))))))

(local
 (defthm left-rotation-preserves-natural-values
   (implies (and (or (not (cdr entry)) (natp (cdr entry)))
                 (data-natural-tree-values-p left) (data-natural-tree-values-p right))
            (data-natural-tree-values-p (boymoo-compiler::table-rotate-left entry left right)))
   :hints (("Goal" :use ((:instance natural-values-in-the-child-trees (tree right)))
                   :in-theory (disable boymoo-compiler::table-node data-natural-tree-values-p)))))

(local
 (defthm right-rotation-preserves-natural-values
   (implies (and (or (not (cdr entry)) (natp (cdr entry)))
                 (data-natural-tree-values-p left) (data-natural-tree-values-p right))
            (data-natural-tree-values-p (boymoo-compiler::table-rotate-right entry left right)))
   :hints (("Goal" :use ((:instance natural-values-in-the-child-trees (tree left)))
                   :in-theory (disable boymoo-compiler::table-node data-natural-tree-values-p)))))

(local
 (defthm balancing-a-tree-preserves-natural-values
   (implies (and (or (not (cdr entry)) (natp (cdr entry)))
                 (data-natural-tree-values-p left) (data-natural-tree-values-p right))
            (data-natural-tree-values-p (boymoo-compiler::table-balance entry left right)))
   :hints (("Goal" :use ((:instance natural-values-in-the-child-trees (tree left))
                         (:instance natural-values-in-the-child-trees (tree right)))
                   :in-theory (disable boymoo-compiler::table-node boymoo-compiler::table-height
                                       boymoo-compiler::table-rotate-left boymoo-compiler::table-rotate-right
                                       data-natural-tree-values-p)))))

(local
 (defthm tree-insertion-preserves-natural-values
   (implies (and (data-natural-tree-values-p tree) (natp value))
            (data-natural-tree-values-p (boymoo-compiler::table-tree-put key value tree)))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-put key value tree)
                   :in-theory (disable boymoo-compiler::table-balance boymoo-compiler::table-node
                                       boymoo-compiler::table-key-less)))))

(local
 (defthm tree-lookup-of-a-natural-value
   (implies (and (data-natural-tree-values-p tree) (boymoo-compiler::table-tree-get key tree))
            (natp (boymoo-compiler::table-tree-get key tree)))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-get key tree)
                   :in-theory (disable boymoo-compiler::table-key-less)))))

(local
 (in-theory (disable boymoo-compiler::table-tree-put boymoo-compiler::table-tree-get
                     boymoo-compiler::text-hash boymoo-compiler::low-bits ash)))

(local
 (defthm table-insertion-preserves-natural-values
   (implies (and (data-natural-table-values-p tree bits) (natp value))
            (data-natural-table-values-p (boymoo-compiler::table-put key value hash bits tree) bits))
   :hints (("Goal" :induct (boymoo-compiler::table-put key value hash bits tree)))))

(local
 (defthm table-lookup-of-a-natural-value
   (implies (and (data-natural-table-values-p tree bits) (boymoo-compiler::table-get key hash bits tree))
            (natp (boymoo-compiler::table-get key hash bits tree)))
   :hints (("Goal" :induct (boymoo-compiler::table-get key hash bits tree)))))

(local
 (in-theory (disable boymoo-compiler::table-get boymoo-compiler::table-put data-natural-table-values-p)))

(defthm data-numbered-package-index-lookup-is-natural
  (implies (and (data-natural-table-values-p packages 12)
                (boymoo-compiler::index-get text packages))
           (natp (boymoo-compiler::index-get text packages)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((boymoo-compiler::index-get text packages)))))

(defthm data-index-set-keeps-natural-number-values
  (implies (and (data-natural-table-values-p packages 12) (natp number))
           (data-natural-table-values-p (boymoo-compiler::index-set text number packages) 12)))

(local (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set boymoo-compiler::decode-part length)))

(defthm data-package-numbers-have-natural-values
  (implies (and (natp next) (data-natural-table-values-p packages 12))
           (data-natural-table-values-p (boymoo-compiler::data-package-numbers lines next packages) 12))
  :hints (("Goal" :induct (boymoo-compiler::data-package-numbers lines next packages))))

; The program pass preserves a vacant or owned home key in a
; well-formed name table.
(defun data-home-available-state-p (number name state-data)
  (and (data-table-p (car state-data) 12)
       (data-symbol-home-available-p number name state-data)))

(local
 (in-theory (disable data-table-p boymoo-compiler::data-bucket-add boymoo-compiler::data-text
                     boymoo-compiler::data-word boymoo-compiler::data-block)))

(defthm data-bucket-add-keeps-name-table
  (equal (car (boymoo-compiler::data-bucket-add number name name-word symbol-word state-data))
         (car state-data))
  :hints (("Goal" :in-theory (enable boymoo-compiler::data-bucket-add))))

(local
 (defthm newly-interned-reference-is-present-and-ordinary
   (implies (not (data-name-table-lookup package name state-data))
            (and (mv-nth 0 (boymoo-compiler::data-intern package name state-data))
                 (not (eq (mv-nth 0 (boymoo-compiler::data-intern package name state-data)) :import))))))

(defthm data-intern-preserves-available-home
  (implies (and (natp number) (stringp query) (natp package) (stringp name)
                (data-home-available-state-p number query state-data))
           (data-home-available-state-p
            number query (mv-nth 2 (boymoo-compiler::data-intern package name state-data))))
  :hints (("Goal" :use newly-interned-reference-is-present-and-ordinary
                  :cases ((and (equal package number) (equal name query))))))

(local
 (in-theory (disable data-home-available-state-p boymoo-compiler::data-intern
                     boymoo-compiler::decode-symbol-part boymoo-compiler::symbol-separator char)))

(defthm data-remember-keeps-available-home
  (equal (data-home-available-state-p number name (boymoo-compiler::data-remember text word state-data))
         (data-home-available-state-p number name state-data))
  :hints (("Goal" :in-theory (enable data-home-available-state-p))))

(defthm data-with-block-keeps-available-home
  (equal (data-home-available-state-p number name (boymoo-compiler::data-with-block block state-data))
         (data-home-available-state-p number name state-data))
  :hints (("Goal" :in-theory (enable data-home-available-state-p))))

(local (in-theory (disable boymoo-compiler::data-remember boymoo-compiler::data-with-block)))

(defthm data-symbol-preserves-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-symbol-storage-input-p text))
           (data-home-available-state-p
            number name (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-symbol data-symbol-storage-input-p
                           boymoo-compiler::data-number boymoo-compiler::decode-part boymoo-compiler::hex-byte)))

(defthm data-atom-preserves-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-atom-storage-input-p text))
           (data-home-available-state-p
            number name (mv-nth 1 (boymoo-compiler::data-atom text packages state-data)))))
