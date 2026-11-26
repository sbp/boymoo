(in-package "BOYMOO-PROOFS")

(include-book "layout")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-compiler::table-key-less
                           boymoo-compiler::label-hash)))

(defun assembly-rank (key ranks)
  (rfix (cdr (assoc-equal key ranks))))

(defun assembly-ranked-pair-p (first second)
  (and (not (equal (car first) (car second)))
       (not (equal (cdr first) (cdr second)))
       (iff (boymoo-compiler::table-key-less (car first) (car second))
            (< (cdr first) (cdr second)))
       (iff (boymoo-compiler::table-key-less (car second) (car first))
            (< (cdr second) (cdr first)))))

(defun assembly-ranked-against-p (entry ranks)
  (if (atom ranks)
      t
    (and (assembly-ranked-pair-p entry (car ranks))
         (assembly-ranked-against-p entry (cdr ranks)))))

(defun assembly-ranking-p (ranks)
  (if (atom ranks)
      (null ranks)
    (and (consp (car ranks))
         (rationalp (cdar ranks))
         (not (boymoo-compiler::table-key-less (caar ranks) (caar ranks)))
         (assembly-ranked-against-p (car ranks) (cdr ranks))
         (assembly-ranking-p (cdr ranks)))))

(local
 (defthm assembly-ranked-against-p-of-lookup
   (implies (and (assembly-ranked-against-p entry ranks)
                 (assoc-equal key ranks))
            (assembly-ranked-pair-p entry (assoc-equal key ranks)))
   :hints (("Goal" :induct (assoc-equal key ranks)
                   :in-theory (disable assembly-ranked-pair-p)))))

(local
 (defthm assembly-rational-rank
   (implies (and (assembly-ranking-p ranks) (assoc-equal key ranks))
            (rationalp (cdr (assoc-equal key ranks))))))

(local
 (defthm assembly-key-of-lookup
   (implies (assoc-equal key ranks)
            (equal (car (assoc-equal key ranks)) key))))

(local
 (defthm assembly-rank-comparison
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal a ranks) (assoc-equal b ranks))
            (and (iff (boymoo-compiler::table-key-less a b)
                      (< (assembly-rank a ranks) (assembly-rank b ranks)))
                 (iff (equal (assembly-rank a ranks) (assembly-rank b ranks))
                      (equal a b))))
   :hints (("Goal" :induct (assembly-ranking-p ranks))
           ("Subgoal *1/2"
            :use ((:instance assembly-ranked-against-p-of-lookup
                             (entry (car ranks)) (ranks (cdr ranks)) (key a))
                  (:instance assembly-ranked-against-p-of-lookup
                             (entry (car ranks)) (ranks (cdr ranks)) (key b)))))
   :rule-classes nil))

(defun assembly-tree-shaped-p (tree)
  (if (atom tree)
      (null tree)
    (and (consp (car tree))
         (consp (cdar tree))
         (posp (caar tree))
         (consp (cdr tree))
         (assembly-tree-shaped-p (cadr tree))
         (assembly-tree-shaped-p (cddr tree)))))

(defun assembly-tree-entries (tree)
  (if (atom tree)
      nil
    (append (assembly-tree-entries (cadr tree))
            (cons (cdar tree) (assembly-tree-entries (cddr tree))))))

(local
 (defthm assembly-tree-height-is-natural
   (implies (assembly-tree-shaped-p tree)
            (natp (boymoo-compiler::table-height tree)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm assembly-tree-node
   (implies (and (consp entry)
                 (assembly-tree-shaped-p left)
                 (assembly-tree-shaped-p right))
            (and (assembly-tree-shaped-p (boymoo-compiler::table-node entry left right))
                 (equal (assembly-tree-entries (boymoo-compiler::table-node entry left right))
                        (append (assembly-tree-entries left)
                                (cons entry (assembly-tree-entries right))))))))

(local (in-theory (disable boymoo-compiler::table-node)))

(local
 (defthm assembly-table-rotate-left
   (implies (and (consp entry) (consp right)
                 (assembly-tree-shaped-p left) (assembly-tree-shaped-p right))
            (and (assembly-tree-shaped-p (boymoo-compiler::table-rotate-left entry left right))
                 (equal (assembly-tree-entries
                         (boymoo-compiler::table-rotate-left entry left right))
                        (append (assembly-tree-entries left)
                                (cons entry (assembly-tree-entries right))))))))

(local
 (defthm assembly-table-rotate-right
   (implies (and (consp entry) (consp left)
                 (assembly-tree-shaped-p left) (assembly-tree-shaped-p right))
            (and (assembly-tree-shaped-p (boymoo-compiler::table-rotate-right entry left right))
                 (equal (assembly-tree-entries
                         (boymoo-compiler::table-rotate-right entry left right))
                        (append (assembly-tree-entries left)
                                (cons entry (assembly-tree-entries right))))))))

(local (in-theory (disable boymoo-compiler::table-rotate-left
                           boymoo-compiler::table-rotate-right)))

(local
 (defthm assembly-height-implies-cons
   (implies (and (assembly-tree-shaped-p tree)
                 (< 0 (boymoo-compiler::table-height tree)))
            (consp tree))
   :rule-classes :forward-chaining))

(local
 (defthm assembly-table-balance
   (implies (and (consp entry)
                 (assembly-tree-shaped-p left) (assembly-tree-shaped-p right))
            (and (assembly-tree-shaped-p (boymoo-compiler::table-balance entry left right))
                 (equal (assembly-tree-entries (boymoo-compiler::table-balance entry left right))
                        (append (assembly-tree-entries left)
                                (cons entry (assembly-tree-entries right))))))))

(local (in-theory (disable boymoo-compiler::table-balance
                           boymoo-compiler::table-height
                           assembly-rank)))

(local
 (defthm assembly-key-less-by-rank
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal a ranks)
                 (assoc-equal b ranks))
            (equal (boymoo-compiler::table-key-less a b)
                   (< (assembly-rank a ranks) (assembly-rank b ranks))))
   :hints (("Goal" :use assembly-rank-comparison))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm assembly-equal-ranks
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal a ranks)
                 (assoc-equal b ranks))
            (equal (equal (assembly-rank a ranks) (assembly-rank b ranks))
                   (equal a b)))
   :hints (("Goal" :use assembly-rank-comparison))
   :rule-classes nil))

(defun assembly-ranked-entries-p (entries ranks)
  (if (atom entries)
      t
    (and (assoc-equal (caar entries) ranks)
         (assembly-ranked-entries-p (cdr entries) ranks))))

(defun assembly-before-p (entries bound ranks)
  (if (atom entries)
      t
    (and (< (assembly-rank (caar entries) ranks) bound)
         (assembly-before-p (cdr entries) bound ranks))))

(defun assembly-after-p (entries bound ranks)
  (if (atom entries)
      t
    (and (< bound (assembly-rank (caar entries) ranks))
         (assembly-after-p (cdr entries) bound ranks))))

(defun assembly-ordered-p (entries ranks)
  (if (atom entries)
      t
    (and (assembly-after-p (cdr entries) (assembly-rank (caar entries) ranks) ranks)
         (assembly-ordered-p (cdr entries) ranks))))

(local
 (defthm assembly-ranked-entries-of-append
   (equal (assembly-ranked-entries-p (append xs ys) ranks)
          (and (assembly-ranked-entries-p xs ranks)
               (assembly-ranked-entries-p ys ranks)))))

(local
 (defthm assembly-after-of-append
   (equal (assembly-after-p (append xs ys) bound ranks)
          (and (assembly-after-p xs bound ranks)
               (assembly-after-p ys bound ranks)))))

(local
 (defthm assembly-after-lower-bound
   (implies (and (rationalp low) (rationalp high) (<= low high)
                 (assembly-after-p xs high ranks))
            (assembly-after-p xs low ranks))
   :hints (("Goal" :induct (assembly-after-p xs high ranks)))
   :rule-classes nil))

(local
 (defthm assembly-ordered-append-node
   (equal (assembly-ordered-p (append xs (cons entry ys)) ranks)
          (and (assembly-ordered-p xs ranks)
               (assembly-ordered-p ys ranks)
               (assembly-before-p xs (assembly-rank (car entry) ranks) ranks)
               (assembly-after-p ys (assembly-rank (car entry) ranks) ranks)))
   :hints (("Goal" :induct (len xs))
           ("Subgoal *1/2"
            :use ((:instance assembly-after-lower-bound
                             (xs ys)
                             (low (assembly-rank (caar xs) ranks))
                             (high (assembly-rank (car entry) ranks))))))))

(defun assembly-ordered-put (key value entries ranks)
  (if (atom entries)
      (list (cons key value))
    (cond ((equal key (caar entries))
           (cons (cons key value) (cdr entries)))
          ((< (assembly-rank key ranks) (assembly-rank (caar entries) ranks))
           (cons (cons key value) entries))
          (t (cons (car entries)
                   (assembly-ordered-put key value (cdr entries) ranks))))))

(local
 (defthm assembly-before-of-ordered-put
   (implies (< (assembly-rank key ranks) bound)
            (equal (assembly-before-p (assembly-ordered-put key value xs ranks) bound ranks)
                   (assembly-before-p xs bound ranks)))))

(local
 (defthm assembly-after-of-ordered-put
   (implies (< bound (assembly-rank key ranks))
            (equal (assembly-after-p (assembly-ordered-put key value xs ranks) bound ranks)
                   (assembly-after-p xs bound ranks)))))

(local
 (defthm assembly-ranked-entries-of-ordered-put
   (implies (and (assembly-ranked-entries-p entries ranks) (assoc-equal key ranks))
            (assembly-ranked-entries-p (assembly-ordered-put key value entries ranks) ranks))))

(local
 (defthm assembly-ordered-of-ordered-put
   (implies (and (assembly-ordered-p entries ranks)
                 (assembly-ranked-entries-p entries ranks)
                 (assoc-equal key ranks)
                 (assembly-ranking-p ranks))
            (assembly-ordered-p (assembly-ordered-put key value entries ranks) ranks))
   :hints (("Goal" :induct (assembly-ordered-put key value entries ranks)
                   :in-theory (disable assembly-ranking-p))
           ("Subgoal *1/4"
            :use ((:instance assembly-equal-ranks
                             (a key) (b (caar entries)))))
           ("Subgoal *1/2"
            :use ((:instance assembly-after-lower-bound
                             (xs (cdr entries)) (low (assembly-rank key ranks))
                             (high (assembly-rank (caar entries) ranks))))))))

(local
 (defthm assembly-ordered-put-before-root
   (implies (< (assembly-rank key ranks) (assembly-rank (car entry) ranks))
            (equal (assembly-ordered-put key value (append xs (cons entry ys)) ranks)
                   (append (assembly-ordered-put key value xs ranks) (cons entry ys))))
   :hints (("Goal" :induct (len xs)))))

(local
 (defthm assembly-ordered-put-after-left
   (implies (and (rationalp bound)
                 (<= bound (assembly-rank key ranks))
                 (assembly-before-p xs bound ranks))
            (equal (assembly-ordered-put key value (append xs ys) ranks)
                   (append xs (assembly-ordered-put key value ys ranks))))
   :hints (("Goal" :induct (len xs)))
   :rule-classes nil))

(defun assembly-tree-p (tree ranks)
  (and (assembly-tree-shaped-p tree)
       (assembly-ranked-entries-p (assembly-tree-entries tree) ranks)
       (assembly-ordered-p (assembly-tree-entries tree) ranks)))

(local
 (defthm assembly-table-tree-put
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal key ranks)
                 (assembly-tree-p tree ranks))
            (and (assembly-tree-shaped-p (boymoo-compiler::table-tree-put key value tree))
                 (equal (assembly-tree-entries (boymoo-compiler::table-tree-put key value tree))
                        (assembly-ordered-put key value (assembly-tree-entries tree) ranks))))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-put key value tree)
                   :in-theory (disable assembly-ranking-p))
           ("Subgoal *1/4"
            :use ((:instance assembly-ordered-put-after-left
                             (xs (assembly-tree-entries (cadr tree)))
                             (ys (cons (cdar tree) (assembly-tree-entries (cddr tree))))
                             (bound (assembly-rank (cadar tree) ranks)))))
           ("Subgoal *1/2"
            :use ((:instance assembly-ordered-put-after-left
                             (xs (assembly-tree-entries (cadr tree)))
                             (ys (cons (cdar tree) (assembly-tree-entries (cddr tree))))
                             (bound (assembly-rank (cadar tree) ranks))))))))

(local
 (defthm assembly-tree-p-of-put
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal key ranks)
                 (assembly-tree-p tree ranks))
            (assembly-tree-p (boymoo-compiler::table-tree-put key value tree) ranks))
   :hints (("Goal" :in-theory (disable boymoo-compiler::table-tree-put
                                      assembly-ranking-p assembly-ordered-put)))))

(local
 (defthm assembly-alist-of-append
   (implies (and (alistp xs) (alistp ys))
            (alistp (append xs ys)))))

(local
 (defthm assembly-tree-entries-are-an-alist
   (implies (assembly-tree-shaped-p tree)
            (alistp (assembly-tree-entries tree)))
   :hints (("Goal" :induct (assembly-tree-entries tree)))))

(local
 (defthm assembly-assoc-of-append
   (implies (alistp xs)
            (equal (assoc-equal key (append xs ys))
                   (or (assoc-equal key xs) (assoc-equal key ys))))
   :hints (("Goal" :induct (append xs ys)))))

(local
 (defthm assembly-assoc-of-ordered-put
   (equal (assoc-equal query (assembly-ordered-put key value entries ranks))
          (if (equal query key)
              (cons key value)
            (assoc-equal query entries)))
   :hints (("Goal" :induct (assembly-ordered-put key value entries ranks)))))

(local
 (defthm assembly-before-excludes-key
   (implies (and (rationalp bound)
                 (<= bound (assembly-rank key ranks))
                 (assembly-before-p xs bound ranks))
            (not (assoc-equal key xs)))
   :hints (("Goal" :induct (len xs)))
   :rule-classes nil))

(local
 (defthm assembly-after-excludes-key
   (implies (and (rationalp bound)
                 (<= (assembly-rank key ranks) bound)
                 (assembly-after-p xs bound ranks))
            (not (assoc-equal key xs)))
   :hints (("Goal" :induct (len xs)))
   :rule-classes nil))

(local
 (defthm assembly-get-from-tree
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal key ranks)
                 (assembly-tree-p tree ranks))
            (equal (boymoo-compiler::table-tree-get key tree)
                   (cdr (assoc-equal key (assembly-tree-entries tree)))))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-get key tree)
                   :in-theory (disable assembly-ranking-p))
           ("Subgoal *1/4"
            :use ((:instance assembly-before-excludes-key
                             (xs (assembly-tree-entries (cadr tree)))
                             (bound (assembly-rank (cadar tree) ranks)))))
           ("Subgoal *1/3"
            :use ((:instance assembly-after-excludes-key
                             (xs (assembly-tree-entries (cddr tree)))
                             (bound (assembly-rank (cadar tree) ranks)))))
           ("Subgoal *1/2"
            :use ((:instance assembly-before-excludes-key
                             (xs (assembly-tree-entries (cadr tree)))
                             (bound (assembly-rank (cadar tree) ranks))))))))

(local
 (defthm assembly-tree-get-of-put
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal key ranks)
                 (assoc-equal query ranks)
                 (assembly-tree-p tree ranks))
            (equal (boymoo-compiler::table-tree-get
                    query (boymoo-compiler::table-tree-put key value tree))
                   (if (equal query key)
                       value
                     (boymoo-compiler::table-tree-get query tree))))
   :hints (("Goal"
            :use ((:instance assembly-get-from-tree
                             (key query)
                             (tree (boymoo-compiler::table-tree-put key value tree)))
                  (:instance assembly-get-from-tree (key query)))
            :in-theory (disable boymoo-compiler::table-tree-get
                                boymoo-compiler::table-tree-put
                                assembly-get-from-tree assembly-ranking-p
                                assembly-tree-p assembly-ordered-put)))))

(defun assembly-table-p (bits tree ranks)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) (null tree))
        ((zp bits) (assembly-tree-p tree ranks))
        (t (and (assembly-table-p (1- bits) (car tree) ranks)
                (assembly-table-p (1- bits) (cdr tree) ranks)))))

(local (in-theory (disable assembly-tree-p
                           boymoo-compiler::table-tree-get
                           boymoo-compiler::table-tree-put
                           boymoo-compiler::low-bits ash)))

(local
 (defthm assembly-empty-tree-p
   (assembly-tree-p nil ranks)
   :hints (("Goal" :in-theory (enable assembly-tree-p)))))

(defthm assembly-empty-table-p
  (assembly-table-p bits nil ranks))

(local
 (defthm assembly-get-from-empty-tree
   (equal (boymoo-compiler::table-tree-get key nil) nil)
   :hints (("Goal" :in-theory (enable boymoo-compiler::table-tree-get)))))

(defthm assembly-table-p-of-put
  (implies (and (assembly-ranking-p ranks)
                (assoc-equal key ranks)
                (assembly-table-p bits tree ranks))
           (assembly-table-p bits
                             (boymoo-compiler::table-put key value hash bits tree)
                             ranks))
  :hints (("Goal" :induct (boymoo-compiler::table-put key value hash bits tree)
                  :in-theory (disable assembly-ranking-p))))

(local
 (defun assembly-table-put-induct (bits hash query-hash tree)
   (declare (xargs :measure (nfix bits)))
   (if (zp bits)
       (list query-hash tree)
     (assembly-table-put-induct
      (1- bits) (ash hash -1) (ash query-hash -1)
      (if (equal (boymoo-compiler::low-bits hash 1) 0)
          (car tree)
        (cdr tree))))))

(defthm assembly-table-get-of-put
  (implies (and (assembly-ranking-p ranks)
                (assoc-equal query ranks)
                (assoc-equal key ranks)
                (assembly-table-p bits tree ranks)
                (implies (equal query key) (equal query-hash hash)))
           (equal (boymoo-compiler::table-get
                   query query-hash bits
                   (boymoo-compiler::table-put key value hash bits tree))
                  (if (equal query key)
                      value
                    (boymoo-compiler::table-get query query-hash bits tree))))
  :hints (("Goal" :induct (assembly-table-put-induct bits hash query-hash tree)
                  :expand ((boymoo-compiler::table-get query query-hash bits tree))
                  :in-theory (disable assembly-ranking-p))))

(local (in-theory (disable boymoo-compiler::table-get boymoo-compiler::table-put
                           boymoo-compiler::a64-image-item-size)))

(defun assembly-layout-sizes-p (items)
  (if (atom items)
      t
    (and (natp (boymoo-compiler::a64-image-item-size (car items)))
         (assembly-layout-sizes-p (cdr items)))))

(defun assembly-labels-unused-p (entries table)
  (if (atom entries)
      t
    (and (not (boymoo-compiler::table-get
               (caar entries) (boymoo-compiler::label-hash (caar entries)) 16 table))
         (assembly-labels-unused-p (cdr entries) table))))

(local
 (defthm assembly-unused-labels-after-put
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal key ranks)
                 (assembly-ranked-entries-p entries ranks)
                 (assembly-table-p 16 table ranks)
                 (not (member-equal key (assembly-keys entries)))
                 (assembly-labels-unused-p entries table))
            (assembly-labels-unused-p
             entries (boymoo-compiler::table-put
                      key value (boymoo-compiler::label-hash key) 16 table) ))
   :hints (("Goal" :induct (assembly-labels-unused-p entries table)
                   :in-theory (disable assembly-ranking-p
                                       (:definition assembly-table-p))))))

(defun assembly-layout-input-p (items pc table ranks)
  (let ((entries (assembly-labels items pc)))
    (and (natp pc)
         (assembly-layout-sizes-p items)
         (assembly-ranking-p ranks)
         (assembly-ranked-entries-p entries ranks)
         (no-duplicatesp-equal (assembly-keys entries))
         (assembly-labels-unused-p entries table)
         (assembly-table-p 16 table ranks))))

(defthm assembly-layout-end-and-order
  (implies (assembly-layout-input-p items pc table ranks)
           (mv-let (end labels reversed)
             (boymoo-compiler::a64-layout items pc table rest)
             (and (equal end (+ pc (assembly-size items)))
                  (equal reversed (revappend (assembly-code-items items) rest))
                  (assembly-table-p 16 labels ranks))))
  :hints (("Goal" :induct (boymoo-compiler::a64-layout items pc table rest)
                  :in-theory (disable assembly-ranking-p (:definition assembly-table-p)))))

(local
 (defthm assembly-assoc-implies-key
   (implies (assoc-equal key entries)
            (member-equal key (assembly-keys entries)))
   :rule-classes nil))

(local
 (defthm assembly-associated-label-is-key
   (implies (assoc-equal key (assembly-labels items pc))
            (member-equal key (assembly-keys (assembly-labels items 0))))
   :hints (("Goal" :use ((:instance assembly-assoc-implies-key
                                    (entries (assembly-labels items pc))))))
   :rule-classes :forward-chaining))

(defthm assembly-layout-label-lookup
  (implies (and (assembly-layout-input-p items pc table ranks)
                (assoc-equal query ranks))
           (equal (boymoo-compiler::table-get
                   query (boymoo-compiler::label-hash query) 16
                   (mv-nth 1 (boymoo-compiler::a64-layout items pc table rest)))
                  (if (assoc-equal query (assembly-labels items pc))
                      (cdr (assoc-equal query (assembly-labels items pc)))
                    (boymoo-compiler::table-get
                     query (boymoo-compiler::label-hash query) 16 table))))
  :hints (("Goal" :induct (boymoo-compiler::a64-layout items pc table rest)
                  :in-theory (disable assembly-ranking-p (:definition assembly-table-p)))))

(defthm assembly-label-offset-is-natural
  (implies (and (natp pc)
                (assembly-layout-sizes-p items)
                (assoc-equal query (assembly-labels items pc)))
           (natp (cdr (assoc-equal query (assembly-labels items pc)))))
  :hints (("Goal" :induct (assembly-labels items pc))))

(local
 (defthm assembly-ranked-member
   (implies (and (assembly-ranked-entries-p entries ranks)
                 (assoc-equal key entries))
            (assoc-equal key ranks))
   :rule-classes nil))

(defthm assembly-layout-entry-offset
  (implies (and (assembly-layout-input-p items 0 nil ranks)
                (assoc-equal entry (assembly-labels items 0)))
           (equal (boymoo-compiler::a64-offset
                   entry (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)))
                  (cdr (assoc-equal entry (assembly-labels items 0)))))
  :hints (("Goal" :use ((:instance assembly-layout-label-lookup
                                   (query entry) (pc 0) (table nil) (rest nil))
                        (:instance assembly-ranked-member
                                   (key entry) (entries (assembly-labels items 0))))
                  :in-theory (disable boymoo-compiler::a64-layout
                                      assembly-layout-label-lookup assembly-ranking-p))))

(in-theory (disable assembly-empty-table-p assembly-table-p-of-put assembly-table-get-of-put))
