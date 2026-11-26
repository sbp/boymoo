(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; The static data and front end use textual keys and pairs of a package
; number and a textual name. These are the key domains of this book.
(defun data-table-key-p (key)
  (or (stringp key)
      (and (consp key) (natp (car key)) (stringp (cdr key)))))

(local
 (defun text-comparison-induction (index count)
   (declare (xargs :measure (nfix count)))
   (if (zp count) index
     (text-comparison-induction (1+ index) (1- count)))))

(local
 (defthm character-listp-of-coerce
   (implies (stringp text) (character-listp (coerce text 'list)))))

(local
 (defthm characterp-of-nth-in-range
   (implies (and (character-listp chars) (natp index) (< index (len chars)))
            (characterp (nth index chars)))))

(local
 (defthm characterp-of-char-in-range
   (implies (and (stringp text) (natp index) (< index (length text)))
            (characterp (char text index)))))

(local
 (defthm character-by-code
   (implies (and (characterp a) (characterp b))
            (equal (equal (char-code a) (char-code b)) (equal a b)))
   :hints (("Goal" :use ((:instance acl2::code-char-char-code-is-identity (acl2::c a))
                        (:instance acl2::code-char-char-code-is-identity (acl2::c b)))
                   :in-theory (disable acl2::code-char-char-code-is-identity)))))

(local
 (defthm text-characters-less-transitive
   (implies (and (stringp a) (stringp b) (stringp c)
                 (natp i) (integerp count)
                 (<= (+ i count) (length a))
                 (<= (+ i count) (length b))
                 (<= (+ i count) (length c))
                 (boymoo-compiler::table-string-less a b i count)
                 (boymoo-compiler::table-string-less b c i count))
            (boymoo-compiler::table-string-less a c i count))
   :hints (("Goal" :induct (text-comparison-induction i count)
                   :in-theory (disable char length)))))

(local
 (defthm text-characters-less-reverse
   (implies (and (stringp a) (stringp b)
                 (natp i) (integerp count)
                 (<= (+ i count) (length a))
                 (<= (+ i count) (length b))
                 (boymoo-compiler::table-string-less a b i count))
            (not (boymoo-compiler::table-string-less b a i count)))
   :hints (("Goal" :induct (text-comparison-induction i count)
                   :in-theory (disable char length)))))

(local
 (defthm compare-equal-characters
   (not (boymoo-compiler::table-string-less a a i count))
   :hints (("Goal" :induct (text-comparison-induction i count)))))

(local
 (defthm nthcdr-when-at-end
   (implies (and (true-listp xs) (natp index) (<= (len xs) index))
            (equal (nthcdr index xs) nil))
   :hints (("Goal" :induct (nthcdr index xs)))))

(local
 (defthm nthcdr-one-more
   (implies (natp index)
            (equal (nthcdr (+ 1 index) xs) (cdr (nthcdr index xs))))
   :hints (("Goal" :induct (nthcdr index xs)))))

(local
 (defthm car-of-nthcdr
   (equal (car (nthcdr index xs)) (nth index xs))
   :hints (("Goal" :induct (nthcdr index xs)))))

(local
 (defthm consp-of-nthcdr-in-range
   (implies (and (natp index) (< index (len xs)))
            (consp (nthcdr index xs)))
   :hints (("Goal" :induct (nthcdr index xs)))))

(local
 (defthm cons-equality-by-fields
   (implies (and (consp xs) (consp ys)
                 (equal (car xs) (car ys)) (equal (cdr xs) (cdr ys)))
            (equal xs ys))
   :rule-classes nil
   :hints (("Goal" :use ((:instance acl2::cons-car-cdr (acl2::x xs))
                        (:instance acl2::cons-car-cdr (acl2::x ys)))
                   :in-theory (disable acl2::cons-car-cdr)))))

(local
 (defthm text-characters-less-complete
   (implies (and (stringp a) (stringp b)
                 (natp i) (natp count)
                 (equal (+ i count) (length a))
                 (equal (+ i count) (length b))
                 (not (equal (nthcdr i (coerce a 'list))
                             (nthcdr i (coerce b 'list))))
                 (not (boymoo-compiler::table-string-less a b i count)))
            (boymoo-compiler::table-string-less b a i count))
   :hints (("Goal" :induct (text-comparison-induction i count)
                   :in-theory (disable nthcdr))
           ("Subgoal *1/2.2" :use ((:instance cons-equality-by-fields
                                             (xs (nthcdr i (coerce a 'list)))
                                             (ys (nthcdr i (coerce b 'list)))))))))

(local
 (defthm text-key-less-transitive
   (implies (and (stringp a) (stringp b) (stringp c)
                 (boymoo-compiler::table-text-less a b)
                 (boymoo-compiler::table-text-less b c))
            (boymoo-compiler::table-text-less a c))
   :hints (("Goal" :in-theory (disable boymoo-compiler::table-string-less)))))

(local
 (defthm text-key-less-reverse
   (implies (and (stringp a) (stringp b)
                 (boymoo-compiler::table-text-less a b))
            (not (boymoo-compiler::table-text-less b a)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::table-string-less)))))

(local
 (defthm text-equality-by-characters
   (implies (and (stringp a) (stringp b))
            (equal (equal (coerce a 'list) (coerce b 'list)) (equal a b)))
   :hints (("Goal" :use ((:instance acl2::coerce-inverse-2 (acl2::x a))
                        (:instance acl2::coerce-inverse-2 (acl2::x b)))
                   :in-theory (disable acl2::coerce-inverse-2)))))

(local
 (defthm text-key-less-complete
   (implies (and (stringp a) (stringp b) (not (equal a b))
                 (not (boymoo-compiler::table-text-less a b)))
            (boymoo-compiler::table-text-less b a))
   :hints (("Goal" :use ((:instance text-characters-less-complete
                                    (i 0) (count (length a))))
                   :in-theory (disable boymoo-compiler::table-string-less
                                       text-characters-less-complete)))))

(local
 (defthm compare-equal-text
   (not (boymoo-compiler::table-text-less a a))))

(local (in-theory (disable boymoo-compiler::table-text-less)))

(defthmd data-key-less-transitive
  (implies (and (data-table-key-p a) (data-table-key-p b) (data-table-key-p c)
                (boymoo-compiler::table-key-less a b)
                (boymoo-compiler::table-key-less b c))
           (boymoo-compiler::table-key-less a c)))

(defthm data-key-less-reverse
  (implies (and (data-table-key-p a) (data-table-key-p b)
                (boymoo-compiler::table-key-less a b))
           (not (boymoo-compiler::table-key-less b a))))

(defthm data-key-less-complete
  (implies (and (data-table-key-p a) (data-table-key-p b)
                (not (equal a b)) (not (boymoo-compiler::table-key-less a b)))
           (boymoo-compiler::table-key-less b a)))

(defthm data-key-less-irreflexive
  (implies (data-table-key-p a)
           (not (boymoo-compiler::table-key-less a a))))

(local
 (defthm data-key-is-non-nil
   (implies (data-table-key-p key) (not (equal key nil)))
   :rule-classes :forward-chaining))

(local (in-theory (disable boymoo-compiler::table-key-less data-table-key-p)))

(defun data-entry-keys-after-p (key entries)
  (if (atom entries)
      t
    (and (boymoo-compiler::table-key-less key (caar entries))
         (data-entry-keys-after-p key (cdr entries)))))

(defun data-entry-keys-before-p (entries key)
  (if (atom entries)
      t
    (and (boymoo-compiler::table-key-less (caar entries) key)
         (data-entry-keys-before-p (cdr entries) key))))

(defun data-ordered-entries-p (entries)
  (if (atom entries)
      (null entries)
    (and (consp (car entries))
         (data-table-key-p (caar entries))
         (data-entry-keys-after-p (caar entries) (cdr entries))
         (data-ordered-entries-p (cdr entries)))))

(defun data-ordered-entry-put (entry entries)
  (cond ((atom entries) (list entry))
        ((equal (car entry) (caar entries)) (cons entry (cdr entries)))
        ((boymoo-compiler::table-key-less (car entry) (caar entries))
         (cons entry entries))
        (t (cons (car entries) (data-ordered-entry-put entry (cdr entries))))))

(local
 (defthm data-append-associative
   (equal (append (append first second) third) (append first second third))))

(local
 (defthm data-append-nil
   (implies (true-listp xs) (equal (append xs nil) xs))))

(local
 (defthm assoc-of-data-append
   (implies key
            (equal (assoc-equal key (append first second))
                   (or (assoc-equal key first) (assoc-equal key second))))))

(local
 (defthm keys-after-of-append
   (equal (data-entry-keys-after-p key (append first second))
          (and (data-entry-keys-after-p key first)
               (data-entry-keys-after-p key second)))))

(local
 (defthm keys-before-of-append
   (equal (data-entry-keys-before-p (append first second) key)
          (and (data-entry-keys-before-p first key)
               (data-entry-keys-before-p second key)))))

(local
 (defthm ordered-entries-split
   (implies (and (true-listp prefix)
                 (data-ordered-entries-p (append prefix (cons entry suffix))))
            (and (data-ordered-entries-p prefix)
                 (data-entry-keys-before-p prefix (car entry))
                 (data-table-key-p (car entry))
                 (data-entry-keys-after-p (car entry) suffix)
                 (data-ordered-entries-p suffix)))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((data-ordered-entries-p (append prefix (cons entry suffix))))))
   :hints (("Goal" :induct (append prefix suffix)))))

(local
 (defthm after-p-transitive
   (implies (and (data-ordered-entries-p entries)
                 (data-table-key-p first) (data-table-key-p second)
                 (boymoo-compiler::table-key-less first second)
                 (data-entry-keys-after-p second entries))
            (data-entry-keys-after-p first entries))
   :hints (("Goal" :induct (data-ordered-entries-p entries)
                   :in-theory (enable data-key-less-transitive)))))

(local
 (defthm before-p-transitive
   (implies (and (data-ordered-entries-p entries)
                 (data-table-key-p first) (data-table-key-p second)
                 (boymoo-compiler::table-key-less first second)
                 (data-entry-keys-before-p entries first))
            (data-entry-keys-before-p entries second))
   :hints (("Goal" :induct (data-ordered-entries-p entries)
                   :in-theory (enable data-key-less-transitive)))))

(local
 (defthm keys-after-of-ordered-put
   (implies (and (boymoo-compiler::table-key-less key (car entry))
                 (data-entry-keys-after-p key entries))
            (data-entry-keys-after-p key (data-ordered-entry-put entry entries)))))

(defthm data-ordered-entries-of-put
  (implies (and (data-ordered-entries-p entries)
                (consp entry) (data-table-key-p (car entry)))
           (data-ordered-entries-p (data-ordered-entry-put entry entries)))
  :hints (("Goal" :induct (data-ordered-entry-put entry entries))))

(local
 (defthm ordered-put-before-end
   (implies (and (not (equal (car entry) (car next)))
                 (boymoo-compiler::table-key-less (car entry) (car next)))
            (equal (data-ordered-entry-put entry (append prefix (cons next suffix)))
                   (append (data-ordered-entry-put entry prefix) (cons next suffix))))
   :hints (("Goal" :induct (append prefix suffix)))))

(local
 (defthm ordered-put-after-prefix
   (implies (and (data-table-key-p (car entry))
                 (data-ordered-entries-p prefix)
                 (data-entry-keys-before-p prefix (car entry)))
            (equal (data-ordered-entry-put entry (append prefix suffix))
                   (append prefix (data-ordered-entry-put entry suffix))))
   :hints (("Goal" :induct (append prefix suffix)))))

(defthm data-assoc-of-ordered-put
  (implies (consp entry)
           (equal (assoc-equal key (data-ordered-entry-put entry entries))
                  (if (equal key (car entry)) entry (assoc-equal key entries))))
  :hints (("Goal" :induct (data-ordered-entry-put entry entries))))

(defun data-tree-entries (tree)
  (if (atom tree)
      nil
    (append (data-tree-entries (cadr tree)) (list (cdar tree))
            (data-tree-entries (cddr tree)))))

(defun data-tree-shape-p (tree)
  (if (atom tree)
      (null tree)
    (and (consp (car tree)) (consp (cdr tree))
         (natp (caar tree))
         (consp (cdar tree))
         (data-tree-shape-p (cadr tree))
         (data-tree-shape-p (cddr tree)))))

(defun data-search-tree-p (tree)
  (and (data-tree-shape-p tree)
       (data-ordered-entries-p (data-tree-entries tree))))

(local
 (defthm true-listp-of-tree-entries
   (true-listp (data-tree-entries tree))))

(local
 (defthm shape-of-table-node
   (implies (and (consp entry) (data-tree-shape-p left) (data-tree-shape-p right))
            (data-tree-shape-p (boymoo-compiler::table-node entry left right)))))

(local
 (defthm entries-of-table-node
   (equal (data-tree-entries (boymoo-compiler::table-node entry left right))
          (append (data-tree-entries left) (cons entry (data-tree-entries right))))))

(local
 (defthm fields-of-table-node
   (and (consp (boymoo-compiler::table-node entry left right))
        (equal (cdar (boymoo-compiler::table-node entry left right)) entry)
        (equal (cadr (boymoo-compiler::table-node entry left right)) left)
        (equal (cddr (boymoo-compiler::table-node entry left right)) right))))

(local (in-theory (disable boymoo-compiler::table-node)))

(local
 (defthm shape-of-tree-children
   (implies (data-tree-shape-p tree)
            (and (data-tree-shape-p (cadr tree))
                 (data-tree-shape-p (cddr tree))))))

(local
 (defthm entry-of-shaped-tree
   (implies (and (data-tree-shape-p tree) (consp tree))
            (consp (cdar tree)))))

(local
 (defthm tree-height-is-natural
   (implies (data-tree-shape-p tree)
            (natp (boymoo-compiler::table-height tree)))
   :rule-classes :type-prescription))

(local
 (defthm taller-tree-has-node
   (implies (and (data-tree-shape-p lower) (data-tree-shape-p higher)
                 (< (boymoo-compiler::table-height lower)
                    (boymoo-compiler::table-height higher)))
            (consp higher))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((< (boymoo-compiler::table-height lower)
                                      (boymoo-compiler::table-height higher)))))))

(local
 (defthm much-taller-tree-has-node
   (implies (and (data-tree-shape-p lower) (data-tree-shape-p higher)
                 (< (+ 1 (boymoo-compiler::table-height lower))
                    (boymoo-compiler::table-height higher)))
            (consp higher))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((< (+ 1 (boymoo-compiler::table-height lower))
                                      (boymoo-compiler::table-height higher)))))))

(local
 (in-theory (disable data-tree-shape-p boymoo-compiler::table-height)))

(local
 (defthm balance-inner-left-has-node
   (implies (and (data-tree-shape-p tree)
                 (< (boymoo-compiler::table-height (cadr tree))
                    (boymoo-compiler::table-height (cddr tree))))
            (consp (cddr tree)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use ((:instance taller-tree-has-node
                                    (lower (cadr tree)) (higher (cddr tree))))))))

(local
 (defthm balance-inner-right-has-node
   (implies (and (data-tree-shape-p tree)
                 (< (boymoo-compiler::table-height (cddr tree))
                    (boymoo-compiler::table-height (cadr tree))))
            (consp (cadr tree)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use ((:instance taller-tree-has-node
                                    (lower (cddr tree)) (higher (cadr tree))))))))

(local
 (defthm shape-of-table-rotations
   (implies (and (consp entry) (data-tree-shape-p left) (data-tree-shape-p right))
            (and (implies (consp right)
                          (data-tree-shape-p (boymoo-compiler::table-rotate-left entry left right)))
                 (implies (consp left)
                          (data-tree-shape-p (boymoo-compiler::table-rotate-right entry left right)))))))

(local
 (defthm entries-of-table-rotate-left
   (implies (consp right)
            (equal (data-tree-entries (boymoo-compiler::table-rotate-left entry left right))
                   (append (data-tree-entries left) (cons entry (data-tree-entries right)))))
   :hints (("Goal" :expand ((data-tree-entries right))
                   :in-theory (disable data-tree-entries)))))

(local
 (defthm entries-of-table-rotate-right
   (implies (consp left)
            (equal (data-tree-entries (boymoo-compiler::table-rotate-right entry left right))
                   (append (data-tree-entries left) (cons entry (data-tree-entries right)))))
   :hints (("Goal" :expand ((data-tree-entries left))
                   :in-theory (disable data-tree-entries)))))

(local
 (defthm rotations-are-nodes
   (and (consp (boymoo-compiler::table-rotate-left entry left right))
        (consp (boymoo-compiler::table-rotate-right entry left right)))))

(local
 (in-theory (disable boymoo-compiler::table-rotate-left boymoo-compiler::table-rotate-right)))

(local
 (defthm shape-of-table-balance
   (implies (and (consp entry) (data-tree-shape-p left) (data-tree-shape-p right))
            (data-tree-shape-p (boymoo-compiler::table-balance entry left right)))))

(local
 (defthm entries-of-table-balance
   (implies (and (data-tree-shape-p left) (data-tree-shape-p right))
            (equal (data-tree-entries (boymoo-compiler::table-balance entry left right))
                   (append (data-tree-entries left) (cons entry (data-tree-entries right)))))))

(local (in-theory (disable boymoo-compiler::table-balance)))

(local
 (defthm shape-of-table-put
   (implies (data-tree-shape-p tree)
            (data-tree-shape-p (boymoo-compiler::table-tree-put key value tree)))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-put key value tree)
                   :in-theory (enable data-tree-shape-p)))))

(local
 (defthm assoc-when-keys-are-after
   (implies (and (data-table-key-p key) (data-table-key-p bound)
                 (data-entry-keys-after-p bound entries)
                 (or (equal key bound) (boymoo-compiler::table-key-less key bound)))
            (equal (assoc-equal key entries) nil))))

(local
 (defthm assoc-when-keys-are-before
   (implies (and (data-table-key-p key) (data-table-key-p bound)
                 (data-entry-keys-before-p entries bound)
                 (not (boymoo-compiler::table-key-less key bound)))
            (equal (assoc-equal key entries) nil))))

(local
 (defthm entries-of-nonempty-tree
   (implies (and (syntaxp (symbolp tree)) (consp tree))
            (equal (data-tree-entries tree)
                   (append (data-tree-entries (cadr tree))
                           (cons (cdar tree) (data-tree-entries (cddr tree))))))))

(local
 (defthm entries-of-empty-tree
   (implies (atom tree) (equal (data-tree-entries tree) nil))))

(defthmd data-tree-get-is-assoc
  (implies (and (data-table-key-p key) (data-search-tree-p tree))
           (equal (boymoo-compiler::table-tree-get key tree)
                  (cdr (assoc-equal key (data-tree-entries tree)))))
  :hints (("Goal" :induct (boymoo-compiler::table-tree-get key tree)
                  :in-theory (disable (:definition data-tree-entries)))))

(defthmd data-tree-put-is-ordered-put
  (implies (and (data-table-key-p key) (data-search-tree-p tree))
           (equal (data-tree-entries (boymoo-compiler::table-tree-put key value tree))
                  (data-ordered-entry-put (cons key value) (data-tree-entries tree))))
  :hints (("Goal" :induct (boymoo-compiler::table-tree-put key value tree)
                  :in-theory (disable (:definition data-tree-entries)))))

(local (in-theory (disable boymoo-compiler::table-tree-put boymoo-compiler::table-tree-get)))

(defthm data-search-tree-p-of-put
  (implies (and (data-table-key-p key) (data-search-tree-p tree))
           (data-search-tree-p (boymoo-compiler::table-tree-put key value tree)))
  :hints (("Goal" :in-theory (enable data-tree-put-is-ordered-put))))

(defthm data-tree-get-after-put
  (implies (and (data-table-key-p query) (data-table-key-p key)
                (data-search-tree-p tree))
           (equal (boymoo-compiler::table-tree-get
                   query (boymoo-compiler::table-tree-put key value tree))
                  (if (equal query key) value (boymoo-compiler::table-tree-get query tree))))
  :hints (("Goal" :in-theory (enable data-tree-get-is-assoc data-tree-put-is-ordered-put))))

(defun data-table-p (tree bits)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) (null tree))
        ((zp bits) (data-search-tree-p tree))
        (t (and (data-table-p (car tree) (1- bits))
                (data-table-p (cdr tree) (1- bits))))))

(defthm data-table-p-of-empty
  (data-table-p nil bits))

(local
 (defthm data-search-tree-p-of-empty
   (data-search-tree-p nil)))

(local
 (defthm table-tree-get-of-empty
   (equal (boymoo-compiler::table-tree-get key nil) nil)
   :hints (("Goal" :in-theory (enable boymoo-compiler::table-tree-get)))))

(local
 (in-theory (disable data-search-tree-p boymoo-compiler::low-bits ash)))

(defthm data-table-p-of-put
  (implies (and (data-table-key-p key) (data-table-p tree bits))
           (data-table-p (boymoo-compiler::table-put key value hash bits tree) bits))
  :hints (("Goal" :induct (boymoo-compiler::table-put key value hash bits tree))))

(local
 (defun data-hash-update-induction (query-hash hash bits tree)
   (declare (xargs :measure (nfix bits)))
   (if (zp bits)
       (list query-hash hash tree)
     (data-hash-update-induction (ash query-hash -1) (ash hash -1) (1- bits)
      (if (equal (boymoo-compiler::low-bits hash 1) 0) (car tree) (cdr tree))))))

(defthm data-table-get-after-put
  (implies (and (data-table-key-p query) (data-table-key-p key)
                (data-table-p tree bits)
                (implies (equal query key) (equal query-hash hash)))
           (equal (boymoo-compiler::table-get
                   query query-hash bits (boymoo-compiler::table-put key value hash bits tree))
                  (if (equal query key) value
                    (boymoo-compiler::table-get query query-hash bits tree))))
  :hints (("Goal" :induct (data-hash-update-induction query-hash hash bits tree))))

(local
 (in-theory (disable boymoo-compiler::table-get boymoo-compiler::table-put
                    boymoo-compiler::text-hash data-table-p)))

(defthm data-index-p-of-set
  (implies (and (stringp key) (data-table-p index 12))
           (data-table-p (boymoo-compiler::index-set key value index) 12))
  :hints (("Goal" :in-theory (enable data-table-key-p))))

(defthm data-index-get-after-set
  (implies (and (stringp query) (stringp key) (data-table-p index 12))
           (equal (boymoo-compiler::index-get query (boymoo-compiler::index-set key value index))
                  (if (equal query key) value (boymoo-compiler::index-get query index))))
  :hints (("Goal" :in-theory (enable data-table-key-p))))

(defthm data-index-get-of-empty
  (equal (boymoo-compiler::index-get key nil) nil)
  :hints (("Goal" :in-theory (enable boymoo-compiler::table-get))))

; Enumerate the entries in hash-tree order and in search-tree order
; within each leaf. This enumeration includes entries with value NIL.
(defun data-table-bindings (tree bits)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) nil)
        ((zp bits) (data-tree-entries tree))
        (t (append (data-table-bindings (car tree) (1- bits))
                   (data-table-bindings (cdr tree) (1- bits))))))

(defthm data-table-bindings-are-a-list
  (true-listp (data-table-bindings tree bits)))
