(in-package "BOYMOO-PROOFS")

(include-book "scope-order")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::table-tree-get boymoo-compiler::table-tree-put
                    boymoo-compiler::table-node boymoo-compiler::table-height boymoo-compiler::table-balance
                    boymoo-compiler::table-rotate-left boymoo-compiler::table-rotate-right
                    boymoo-compiler::table-key-less boymoo-compiler::table-text-less))

(defund generated-scope-key-between-p (key lower upper)
  (and (stringp key)
       (or (null lower) (and (stringp lower) (boymoo-compiler::table-text-less lower key)))
       (or (null upper) (and (stringp upper) (boymoo-compiler::table-text-less key upper)))))

(defund generated-scope-tree-p (tree lower upper)
  (if (atom tree)
      (null tree)
    (let ((key (cadar tree)))
      (and (generated-scope-key-between-p key lower upper)
           (posp (boymoo-compiler::table-height tree))
           (generated-scope-tree-p (cadr tree) lower key)
           (generated-scope-tree-p (cddr tree) key upper)))))

(local
 (defthm generated-scope-tree-height-is-natural
   (implies (generated-scope-tree-p tree lower upper)
            (and (natp (boymoo-compiler::table-height tree))
                 (implies (atom tree) (equal (boymoo-compiler::table-height tree) 0))))
   :hints (("Goal" :expand (generated-scope-tree-p tree lower upper)
                   :in-theory (enable boymoo-compiler::table-height)))
   :rule-classes nil))

(local
 (defthm generated-scope-node-ordered-children
   (equal (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper)
          (and (generated-scope-key-between-p (car entry) lower upper)
               (generated-scope-tree-p left lower (car entry))
               (generated-scope-tree-p right (car entry) upper)))
   :hints (("Goal"
            :use ((:instance generated-scope-tree-height-is-natural (tree left) (upper (car entry)))
                  (:instance generated-scope-tree-height-is-natural (tree right) (lower (car entry))))
            :in-theory (enable generated-scope-tree-p boymoo-compiler::table-node boymoo-compiler::table-height)))))

(local
 (defthm generated-scope-node-lookup
   (equal (boymoo-compiler::table-tree-get key (boymoo-compiler::table-node entry left right))
          (cond ((equal key (car entry)) (cdr entry))
                ((boymoo-compiler::table-key-less key (car entry)) (boymoo-compiler::table-tree-get key left))
                (t (boymoo-compiler::table-tree-get key right))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::table-tree-get boymoo-compiler::table-node)))))

(local
 (defthmd generated-scope-tree-of-nonempty-node
   (implies (and (consp tree)
                 (syntaxp (symbolp tree)))
            (equal (generated-scope-tree-p tree lower upper)
                   (and (generated-scope-key-between-p (cadar tree) lower upper)
                        (posp (boymoo-compiler::table-height tree))
                        (generated-scope-tree-p (cadr tree) lower (cadar tree))
                        (generated-scope-tree-p (cddr tree) (cadar tree) upper))))
   :hints (("Goal" :expand (generated-scope-tree-p tree lower upper)))))

(local
 (defthmd generated-scope-lookup-of-nonempty-node
   (implies (and (consp tree)
                 (syntaxp (symbolp tree)))
            (equal (boymoo-compiler::table-tree-get key tree)
                   (cond ((equal key (cadar tree)) (cddar tree))
                         ((boymoo-compiler::table-key-less key (cadar tree))
                          (boymoo-compiler::table-tree-get key (cadr tree)))
                         (t (boymoo-compiler::table-tree-get key (cddr tree))))))
   :hints (("Goal" :expand (boymoo-compiler::table-tree-get key tree)))))

(local
 (defthm generated-scope-key-between-wider-upper
   (implies (and (generated-scope-key-between-p key lower current) (stringp current)
                 (or (null upper) (and (stringp upper) (boymoo-compiler::table-text-less current upper))))
            (generated-scope-key-between-p key lower upper))
   :hints (("Goal" :use (:instance generated-scope-string-order-transitive
                                    (first key) (second current) (third upper))
                   :in-theory (enable generated-scope-key-between-p)))
   :rule-classes nil))

(local
 (defthm generated-scope-key-between-wider-lower
   (implies (and (generated-scope-key-between-p key current upper) (stringp current)
                 (or (null lower) (and (stringp lower) (boymoo-compiler::table-text-less lower current))))
            (generated-scope-key-between-p key lower upper))
   :hints (("Goal" :use (:instance generated-scope-string-order-transitive
                                    (first lower) (second current) (third key))
                   :in-theory (enable generated-scope-key-between-p)))
   :rule-classes nil))

(local
 (defthm generated-scope-left-rotation-preserves-bounds
   (implies (and (consp right)
                 (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper))
            (generated-scope-tree-p (boymoo-compiler::table-rotate-left entry left right) lower upper))
   :hints (("Goal"
            :use (:instance generated-scope-key-between-wider-lower (key (cadar right)) (current (car entry)))
            :in-theory (enable boymoo-compiler::table-rotate-left generated-scope-key-between-p
                               generated-scope-tree-of-nonempty-node)))
   :rule-classes nil))

(local
 (defthm generated-scope-right-rotation-preserves-bounds
   (implies (and (consp left)
                 (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper))
            (generated-scope-tree-p (boymoo-compiler::table-rotate-right entry left right) lower upper))
   :hints (("Goal"
            :use (:instance generated-scope-key-between-wider-upper (key (cadar left)) (current (car entry)))
            :in-theory (enable boymoo-compiler::table-rotate-right generated-scope-key-between-p
                               generated-scope-tree-of-nonempty-node)))
   :rule-classes nil))

(local
 (defthm generated-scope-left-rotation-preserves-lookup
   (implies (and (consp right) (stringp query) (stringp (car entry)) (stringp (cadar right))
                 (boymoo-compiler::table-text-less (car entry) (cadar right)))
            (equal (boymoo-compiler::table-tree-get query (boymoo-compiler::table-rotate-left entry left right))
                   (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))
   :hints (("Goal"
            :use ((:instance generated-scope-string-order-transitive
                             (first query) (second (car entry)) (third (cadar right)))
                  (:instance generated-scope-string-order-asymmetric
                             (first (car entry)) (second (cadar right))))
            :in-theory (enable boymoo-compiler::table-rotate-left generated-scope-lookup-of-nonempty-node)))
   :rule-classes nil))

(local
 (defthm generated-scope-right-rotation-preserves-lookup
   (implies (and (consp left) (stringp query) (stringp (car entry)) (stringp (cadar left))
                 (boymoo-compiler::table-text-less (cadar left) (car entry)))
            (equal (boymoo-compiler::table-tree-get query (boymoo-compiler::table-rotate-right entry left right))
                   (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))
   :hints (("Goal"
            :use ((:instance generated-scope-string-order-transitive
                             (first query) (second (cadar left)) (third (car entry)))
                  (:instance generated-scope-string-order-asymmetric
                             (first (cadar left)) (second (car entry))))
            :in-theory (enable boymoo-compiler::table-rotate-right generated-scope-lookup-of-nonempty-node)))
   :rule-classes nil))

(local
 (defthm generated-scope-left-rotation-correct
   (let ((rotated (boymoo-compiler::table-rotate-left entry left right)))
     (implies (and (consp right) (stringp query)
                   (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper))
              (and (consp rotated)
                   (generated-scope-tree-p rotated lower upper)
                   (equal (boymoo-compiler::table-tree-get query rotated)
                          (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))))
   :hints (("Goal"
            :use (generated-scope-left-rotation-preserves-bounds generated-scope-left-rotation-preserves-lookup)
            :in-theory (enable boymoo-compiler::table-rotate-left generated-scope-tree-of-nonempty-node
                               generated-scope-key-between-p)))
   :rule-classes nil))

(local
 (defthm generated-scope-right-rotation-correct
   (let ((rotated (boymoo-compiler::table-rotate-right entry left right)))
     (implies (and (consp left) (stringp query)
                   (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper))
              (and (consp rotated)
                   (generated-scope-tree-p rotated lower upper)
                   (equal (boymoo-compiler::table-tree-get query rotated)
                          (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))))
   :hints (("Goal"
            :use (generated-scope-right-rotation-preserves-bounds generated-scope-right-rotation-preserves-lookup)
            :in-theory (enable boymoo-compiler::table-rotate-right generated-scope-tree-of-nonempty-node
                               generated-scope-key-between-p)))
   :rule-classes nil))

(local
 (defthm generated-rebuilding-scope-node-keeps-keys
   (let ((rebuilt (boymoo-compiler::table-node (cdar tree) (cadr tree) (cddr tree))))
     (implies (consp tree)
              (and (implies (generated-scope-tree-p tree lower upper)
                            (generated-scope-tree-p rebuilt lower upper))
                   (equal (boymoo-compiler::table-tree-get query rebuilt)
                          (boymoo-compiler::table-tree-get query tree)))))
   :hints (("Goal" :in-theory (enable generated-scope-tree-of-nonempty-node
                                     generated-scope-lookup-of-nonempty-node)))
   :rule-classes nil))

(local
 (defthm generated-scope-left-then-right-rotation-correct
   (let* ((new-left (boymoo-compiler::table-rotate-left (cdar left) (cadr left) (cddr left)))
          (rotated (boymoo-compiler::table-rotate-right entry new-left right)))
     (implies (and (consp left) (consp (cddr left)) (stringp query)
                   (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper))
              (and (generated-scope-tree-p rotated lower upper)
                   (equal (boymoo-compiler::table-tree-get query rotated)
                          (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))))
   :hints (("Goal"
            :use ((:instance generated-rebuilding-scope-node-keeps-keys (tree left) (upper (car entry)))
                  (:instance generated-scope-left-rotation-correct
                             (entry (cdar left)) (left (cadr left)) (right (cddr left)) (upper (car entry)))
                  (:instance generated-scope-right-rotation-correct
                             (left (boymoo-compiler::table-rotate-left (cdar left) (cadr left) (cddr left)))))))
   :rule-classes nil))

(local
 (defthm generated-scope-right-then-left-rotation-correct
   (let* ((new-right (boymoo-compiler::table-rotate-right (cdar right) (cadr right) (cddr right)))
          (rotated (boymoo-compiler::table-rotate-left entry left new-right)))
     (implies (and (consp right) (consp (cadr right)) (stringp query)
                   (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper))
              (and (generated-scope-tree-p rotated lower upper)
                   (equal (boymoo-compiler::table-tree-get query rotated)
                          (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))))
   :hints (("Goal"
            :use ((:instance generated-rebuilding-scope-node-keeps-keys (tree right) (lower (car entry)))
                  (:instance generated-scope-right-rotation-correct
                             (entry (cdar right)) (left (cadr right)) (right (cddr right)) (lower (car entry)))
                  (:instance generated-scope-left-rotation-correct
                             (right (boymoo-compiler::table-rotate-right (cdar right) (cadr right) (cddr right)))))))
   :rule-classes nil))

(local
 (defthm generated-left-rebalance-has-pivots
   (implies (and (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper)
                 (< (1+ (boymoo-compiler::table-height right)) (boymoo-compiler::table-height left)))
            (and (consp left)
                 (implies (< (boymoo-compiler::table-height (cadr left))
                             (boymoo-compiler::table-height (cddr left)))
                          (consp (cddr left)))))
   :hints (("Goal"
            :use ((:instance generated-scope-tree-height-is-natural (tree left) (upper (car entry)))
                  (:instance generated-scope-tree-height-is-natural (tree right) (lower (car entry)))
                  (:instance generated-scope-tree-height-is-natural (tree (cadr left)) (upper (cadar left)))
                  (:instance generated-scope-tree-height-is-natural
                             (tree (cddr left)) (lower (cadar left)) (upper (car entry))))
            :in-theory (enable generated-scope-tree-of-nonempty-node)))
   :rule-classes nil))

(local
 (defthm generated-right-rebalance-has-pivots
   (implies (and (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper)
                 (< (1+ (boymoo-compiler::table-height left)) (boymoo-compiler::table-height right)))
            (and (consp right)
                 (implies (< (boymoo-compiler::table-height (cddr right))
                             (boymoo-compiler::table-height (cadr right)))
                          (consp (cadr right)))))
   :hints (("Goal"
            :use ((:instance generated-scope-tree-height-is-natural (tree left) (upper (car entry)))
                  (:instance generated-scope-tree-height-is-natural (tree right) (lower (car entry)))
                  (:instance generated-scope-tree-height-is-natural
                             (tree (cadr right)) (lower (car entry)) (upper (cadar right)))
                  (:instance generated-scope-tree-height-is-natural (tree (cddr right)) (lower (cadar right))))
            :in-theory (enable generated-scope-tree-of-nonempty-node)))
   :rule-classes nil))

(local
 (defthm generated-left-rebalance-keeps-bounds-and-lookup
   (let ((balanced (boymoo-compiler::table-balance entry left right)))
     (implies (and (stringp query)
                   (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper)
                   (< (1+ (boymoo-compiler::table-height right)) (boymoo-compiler::table-height left)))
              (and (generated-scope-tree-p balanced lower upper)
                   (equal (boymoo-compiler::table-tree-get query balanced)
                          (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))))
   :hints (("Goal"
            :use (generated-left-rebalance-has-pivots
                  generated-scope-right-rotation-correct generated-scope-left-then-right-rotation-correct)
            :in-theory (enable boymoo-compiler::table-balance)))
   :rule-classes nil))

(local
 (defthm generated-right-rebalance-keeps-bounds-and-lookup
   (let ((balanced (boymoo-compiler::table-balance entry left right)))
     (implies (and (stringp query)
                   (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper)
                   (< (1+ (boymoo-compiler::table-height left)) (boymoo-compiler::table-height right)))
              (and (generated-scope-tree-p balanced lower upper)
                   (equal (boymoo-compiler::table-tree-get query balanced)
                          (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))))
   :hints (("Goal"
            :use (generated-right-rebalance-has-pivots
                  generated-scope-left-rotation-correct generated-scope-right-then-left-rotation-correct)
            :in-theory (enable boymoo-compiler::table-balance)))
   :rule-classes nil))

(local
 (defthm generated-scope-balance-keeps-bounds-and-lookup
   (let ((balanced (boymoo-compiler::table-balance entry left right)))
     (implies (and (stringp query)
                   (generated-scope-tree-p (boymoo-compiler::table-node entry left right) lower upper))
              (and (generated-scope-tree-p balanced lower upper)
                   (equal (boymoo-compiler::table-tree-get query balanced)
                          (boymoo-compiler::table-tree-get query (boymoo-compiler::table-node entry left right))))))
   :hints (("Goal"
            :cases ((< (1+ (boymoo-compiler::table-height right)) (boymoo-compiler::table-height left))
                    (< (1+ (boymoo-compiler::table-height left)) (boymoo-compiler::table-height right)))
            :use (generated-left-rebalance-keeps-bounds-and-lookup generated-right-rebalance-keeps-bounds-and-lookup))
           ("Subgoal 3" :in-theory (enable boymoo-compiler::table-balance)))
   :rule-classes nil))

(local
 (defun generated-scope-insertion-induction (key tree lower upper)
   (if (atom tree)
       (cons lower upper)
     (let ((pivot (cadar tree)))
       (cond ((equal key pivot) (cons lower upper))
             ((boymoo-compiler::table-key-less key pivot)
              (generated-scope-insertion-induction key (cadr tree) lower pivot))
             (t (generated-scope-insertion-induction key (cddr tree) pivot upper)))))))

(defthm generated-scope-insertion-preserves-lookup-and-order
  (let ((after (boymoo-compiler::table-tree-put key value tree)))
    (implies (and (stringp query) (generated-scope-key-between-p key lower upper)
                  (generated-scope-tree-p tree lower upper))
             (and (generated-scope-tree-p after lower upper)
                  (equal (boymoo-compiler::table-tree-get query after)
                         (if (equal query key) value (boymoo-compiler::table-tree-get query tree))))))
  :hints (("Goal"
           :induct (generated-scope-insertion-induction key tree lower upper)
           :in-theory (enable boymoo-compiler::table-tree-put generated-scope-key-between-p
                              generated-scope-tree-of-nonempty-node generated-scope-lookup-of-nonempty-node))
          ("Subgoal *1/3"
           :use (:instance generated-scope-balance-keeps-bounds-and-lookup
                           (entry (cdar tree)) (left (boymoo-compiler::table-tree-put key value (cadr tree)))
                           (right (cddr tree))))
          ("Subgoal *1/4"
           :use ((:instance generated-scope-string-order-total (first key) (second (cadar tree)))
                 (:instance generated-scope-balance-keeps-bounds-and-lookup
                            (entry (cdar tree)) (left (cadr tree))
                            (right (boymoo-compiler::table-tree-put key value (cddr tree))))))
          ("Subgoal *1/1" :in-theory (enable boymoo-compiler::table-tree-put boymoo-compiler::table-tree-get
                                            generated-scope-key-between-p generated-scope-tree-p)))
  :rule-classes nil)
