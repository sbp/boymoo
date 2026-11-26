(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-arity-entry-covered-p (entry names)
  (implies (cdr entry) (member-equal (car entry) names)))

(defun assembly-arity-tree-covered-p (tree names)
  (if (atom tree)
      t
    (and (assembly-arity-entry-covered-p (cdar tree) names)
         (assembly-arity-tree-covered-p (cadr tree) names)
         (assembly-arity-tree-covered-p (cddr tree) names))))

(defun assembly-arity-index-covered-p (index bits names)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom index) t)
        ((zp bits) (assembly-arity-tree-covered-p index names))
        (t (and (assembly-arity-index-covered-p (car index) (1- bits) names)
                (assembly-arity-index-covered-p (cdr index) (1- bits) names)))))

(local (in-theory (disable boymoo-compiler::table-key-less
                           boymoo-compiler::table-height
                           boymoo-compiler::text-hash
                           boymoo-compiler::low-bits ash)))

(local
 (defthm assembly-covered-arity-tree-lookup
   (implies (and (assembly-arity-tree-covered-p tree names)
                 (boymoo-compiler::table-tree-get key tree))
            (member-equal key names))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-get key tree)))
   :rule-classes nil))

(local
 (defthm assembly-covered-arity-table-lookup
   (implies (and (assembly-arity-index-covered-p index bits names)
                 (boymoo-compiler::table-get key hash bits index))
            (member-equal key names))
   :hints (("Goal" :induct (boymoo-compiler::table-get key hash bits index)
                   :in-theory (disable boymoo-compiler::table-tree-get))
           ("Subgoal *1/2" :use ((:instance assembly-covered-arity-tree-lookup (tree index)))))
   :rule-classes nil))

(defthm assembly-covered-arity-index-lookup
  (implies (and (assembly-arity-index-covered-p index 12 names)
                (boymoo-compiler::index-get key index))
           (member-equal key names))
  :hints (("Goal"
           :use ((:instance assembly-covered-arity-table-lookup
                            (bits 12) (hash (boymoo-compiler::text-hash key))))
           :in-theory (disable boymoo-compiler::table-get)))
  :rule-classes nil)

(local
 (defthm assembly-arity-tree-entries-are-covered
   (implies (assembly-arity-tree-covered-p tree names)
            (and (assembly-arity-entry-covered-p (cdar tree) names)
                 (assembly-arity-tree-covered-p (cadr tree) names)
                 (assembly-arity-tree-covered-p (cddr tree) names)))))

(local
 (defthm assembly-arity-entry-covered-of-cons
   (equal (assembly-arity-entry-covered-p (cons key value) names)
          (implies value (member-equal key names)))))

(local (in-theory (disable assembly-arity-entry-covered-p)))

(local
 (defthm assembly-arity-tree-node-covered
   (implies (and (assembly-arity-entry-covered-p entry names)
                 (assembly-arity-tree-covered-p left names)
                 (assembly-arity-tree-covered-p right names))
            (assembly-arity-tree-covered-p (boymoo-compiler::table-node entry left right) names))))

(local
 (defthm assembly-arity-tree-atom-covered
   (implies (atom tree)
            (assembly-arity-tree-covered-p tree names))))

(local (in-theory (disable boymoo-compiler::table-node assembly-arity-tree-covered-p)))

(local
 (defthm assembly-arity-tree-left-covered
   (implies (and (assembly-arity-entry-covered-p entry names)
                 (assembly-arity-tree-covered-p left names)
                 (assembly-arity-tree-covered-p right names))
            (assembly-arity-tree-covered-p
             (boymoo-compiler::table-rotate-left entry left right) names))))

(local
 (defthm assembly-arity-tree-right-covered
   (implies (and (assembly-arity-entry-covered-p entry names)
                 (assembly-arity-tree-covered-p left names)
                 (assembly-arity-tree-covered-p right names))
            (assembly-arity-tree-covered-p
             (boymoo-compiler::table-rotate-right entry left right) names))))

(local
 (defthm assembly-arity-tree-balance-covered
   (implies (and (assembly-arity-entry-covered-p entry names)
                 (assembly-arity-tree-covered-p left names)
                 (assembly-arity-tree-covered-p right names))
            (assembly-arity-tree-covered-p
             (boymoo-compiler::table-balance entry left right) names))
   :hints (("Goal" :in-theory (disable boymoo-compiler::table-rotate-left
                                       boymoo-compiler::table-rotate-right)))))

(local
 (defthm assembly-arity-tree-put-covered
   (implies (and (implies value (member-equal key names))
                 (assembly-arity-tree-covered-p tree names))
            (assembly-arity-tree-covered-p
             (boymoo-compiler::table-tree-put key value tree) names))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-put key value tree)
                   :in-theory (disable boymoo-compiler::table-balance)))))

(local
 (defthm assembly-arity-index-of-empty-table
   (assembly-arity-index-covered-p nil bits names)))

(local
 (defthm assembly-arity-table-put-covered
   (implies (and (implies value (member-equal key names))
                 (assembly-arity-index-covered-p index bits names))
            (assembly-arity-index-covered-p
             (boymoo-compiler::table-put key value hash bits index) bits names))
   :hints (("Goal" :induct (boymoo-compiler::table-put key value hash bits index)
                   :in-theory (disable boymoo-compiler::table-tree-put)))))

(local
 (defthm assembly-arity-index-set-covered
   (implies (and (implies value (member-equal key names))
                 (assembly-arity-index-covered-p index 12 names))
            (assembly-arity-index-covered-p (boymoo-compiler::index-set key value index) 12 names))
   :hints (("Goal" :in-theory (disable boymoo-compiler::table-put
                                       assembly-arity-index-covered-p)))))

(local
 (defthm assembly-arity-tree-covered-by-more-names
   (implies (assembly-arity-tree-covered-p tree names)
            (assembly-arity-tree-covered-p tree (cons name names)))
   :hints (("Goal" :induct (assembly-arity-tree-covered-p tree names)
                   :in-theory (enable assembly-arity-tree-covered-p assembly-arity-entry-covered-p)))))

(local
 (defthm assembly-arity-index-covered-by-more-names
   (implies (assembly-arity-index-covered-p index bits names)
            (assembly-arity-index-covered-p index bits (cons name names)))
   :hints (("Goal" :induct (assembly-arity-index-covered-p index bits names)))))

(local
 (defthm assembly-arity-index-add-definition
   (implies (assembly-arity-index-covered-p index 12 names)
            (assembly-arity-index-covered-p (boymoo-compiler::index-set key value index)
                                             12 (cons key names)))
   :hints (("Goal"
            :use ((:instance assembly-arity-index-set-covered (names (cons key names)))
                  (:instance assembly-arity-index-covered-by-more-names (bits 12) (name key)))
            :in-theory (disable assembly-arity-index-set-covered
                                assembly-arity-index-covered-by-more-names
                                assembly-arity-index-covered-p boymoo-compiler::index-set)))))

(local
 (defthm assembly-arity-result-component-of-cons
   (equal (mv-nth n (cons first rest))
          (if (zp n) first (mv-nth (1- n) rest)))))

(local (in-theory (disable mv-nth)))

(local (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set
                           boymoo-compiler::symbol-separator
                           boymoo-compiler::declaration-list
                           assembly-arity-index-covered-p)))

(local
 (defthm assembly-index-definition-line-covered
   (mv-let (next-defs next-index)
     (boymoo-compiler::index-definition-line items defs index seen)
     (implies (and (assembly-arity-index-covered-p index 12 (strip-cars defs))
                   (true-listp defs) (string-listp (strip-cars defs)))
              (and (assembly-arity-index-covered-p next-index 12 (strip-cars next-defs))
                   (true-listp next-defs) (string-listp (strip-cars next-defs)))))
   :hints (("Goal" :induct (boymoo-compiler::index-definition-line items defs index seen)
                   :in-theory (disable assoc-equal length)))))

(defthm assembly-index-lines-cover-arity-lookups
  (mv-let (next-defs next-index next-attachments next-sources next-packages next-entry next-target)
    (boymoo-compiler::index-lines lines defs index attachments sources packages entry target)
    (declare (ignore next-attachments next-sources next-packages next-entry next-target))
    (implies (and (assembly-arity-index-covered-p index 12 (strip-cars defs))
                  (true-listp defs) (string-listp (strip-cars defs)))
             (and (assembly-arity-index-covered-p next-index 12 (strip-cars next-defs))
                  (true-listp next-defs) (string-listp (strip-cars next-defs)))))
  :hints (("Goal"
           :induct (boymoo-compiler::index-lines lines defs index attachments sources packages entry target)
           :in-theory (disable boymoo-compiler::index-definition-line assoc-equal
                               boymoo-compiler::reverse-onto)))
  :rule-classes nil)
