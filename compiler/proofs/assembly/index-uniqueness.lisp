(in-package "BOYMOO-PROOFS")

(include-book "label-ranks")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-compiler::table-get boymoo-compiler::table-put
                           boymoo-compiler::text-hash assembly-table-p assembly-ranking-p)))

(local
 (defthm assembly-index-table-well-formed-after-set
   (implies (and (assembly-ranking-p ranks) (assoc-equal key ranks)
                 (assembly-table-p 12 index ranks))
            (assembly-table-p 12 (boymoo-compiler::index-set key value index) ranks))
   :hints (("Goal" :in-theory (enable assembly-table-p-of-put)))))

(local
 (defthm assembly-index-lookup-after-set
   (implies (and (assembly-ranking-p ranks)
                 (assoc-equal query ranks) (assoc-equal key ranks)
                 (assembly-table-p 12 index ranks))
            (equal (boymoo-compiler::index-get query (boymoo-compiler::index-set key value index))
                   (if (equal query key) value (boymoo-compiler::index-get query index))))
   :hints (("Goal" :in-theory (enable assembly-table-get-of-put)))
   :rule-classes ((:rewrite :match-free :all))))

(local (in-theory (disable boymoo-compiler::index-set boymoo-compiler::index-get
                           boymoo-compiler::declaration-list boymoo-compiler::symbol-separator)))

(defun assembly-indexed-definitions-p (defs index ranks)
  (if (atom defs)
      t
    (and (assoc-equal (caar defs) ranks)
         (boymoo-compiler::index-get (caar defs) index)
         (assembly-indexed-definitions-p (cdr defs) index ranks))))

(defun assembly-index-definition-invariant-p (defs index ranks)
  (and (no-duplicatesp-equal (strip-cars defs))
       (assembly-table-p 12 index ranks)
       (assembly-indexed-definitions-p defs index ranks)))

(local
 (defthm assembly-definition-name-is-indexed
   (implies (and (assembly-indexed-definitions-p defs index ranks)
                 (member-equal key (strip-cars defs)))
            (boymoo-compiler::index-get key index))
   :hints (("Goal" :induct (len defs)))
   :rule-classes nil))

(local
 (defthm assembly-indexed-definitions-retained-after-set
   (implies (and (assembly-indexed-definitions-p defs index ranks)
                 (assembly-ranking-p ranks) (assoc-equal key ranks) value
                 (assembly-table-p 12 index ranks))
            (assembly-indexed-definitions-p
             defs (boymoo-compiler::index-set key value index) ranks))
   :hints (("Goal" :induct (assembly-indexed-definitions-p defs index ranks)))))

(local
 (defthm assembly-indexed-definition-of-cons
   (equal (assembly-indexed-definitions-p (cons definition defs) index ranks)
          (and (assoc-equal (car definition) ranks)
               (boymoo-compiler::index-get (car definition) index)
               (assembly-indexed-definitions-p defs index ranks)))))

(local
 (defthm assembly-indexed-definitions-extend-with-new-name
   (let* ((name (car definition))
          (updated (boymoo-compiler::index-set name arity index)))
     (implies (and (assembly-index-definition-invariant-p defs index ranks)
                   (assembly-ranking-p ranks) (assoc-equal name ranks)
                   (natp arity) (not (boymoo-compiler::index-get name index)))
              (assembly-index-definition-invariant-p (cons definition defs) updated ranks)))
   :hints (("Goal"
            :use ((:instance assembly-definition-name-is-indexed (key (car definition))))
            :in-theory (disable assembly-indexed-definitions-p)))))

(local
 (defthm assembly-index-definition-invariant-empty
   (assembly-index-definition-invariant-p nil nil ranks)
   :hints (("Goal" :in-theory (enable assembly-empty-table-p)))))

(defun assembly-definition-candidates-ranked-p (items ranks)
  (if (atom items)
      t
    (and (implies (stringp (caar items)) (assoc-equal (caar items) ranks))
         (assembly-definition-candidates-ranked-p (cdr items) ranks))))

(local
 (defthm assembly-definition-candidate-ranks-of-reverse-onto
   (equal (assembly-definition-candidates-ranked-p (boymoo-compiler::reverse-onto items rest) ranks)
          (and (assembly-definition-candidates-ranked-p items ranks)
               (assembly-definition-candidates-ranked-p rest ranks)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto items rest)))))

(local
 (defthm assembly-index-result-component-of-cons
   (equal (mv-nth n (cons first rest))
          (if (zp n) first (mv-nth (1- n) rest)))))

(local (in-theory (disable mv-nth boymoo-compiler::reverse-onto
                           assembly-index-definition-invariant-p)))

(local
 (defthm assembly-index-definition-line-keeps-invariant
   (mv-let (out-defs out-index)
     (boymoo-compiler::index-definition-line items defs index seen)
     (implies (and (assembly-index-definition-invariant-p defs index ranks)
                   (assembly-ranking-p ranks) (assembly-definition-candidates-ranked-p items ranks))
              (assembly-index-definition-invariant-p out-defs out-index ranks)))
   :hints (("Goal" :induct (boymoo-compiler::index-definition-line items defs index seen)
                   :in-theory (disable assoc-equal)))))

(defun assembly-program-candidates-ranked-p (lines ranks)
  (if (atom lines)
      t
    (and (implies (equal (caar lines) "define")
                  (assembly-definition-candidates-ranked-p (cddar lines) ranks))
         (assembly-program-candidates-ranked-p (cdr lines) ranks))))

(local
 (defthm assembly-index-lines-keep-definition-invariant
   (let ((out-defs (mv-nth 0 (boymoo-compiler::index-lines
                              lines defs index attachments sources packages entry target)))
         (out-index (mv-nth 1 (boymoo-compiler::index-lines
                              lines defs index attachments sources packages entry target))))
     (implies (and (assembly-index-definition-invariant-p defs index ranks)
                   (assembly-ranking-p ranks) (assembly-program-candidates-ranked-p lines ranks))
              (assembly-index-definition-invariant-p out-defs out-index ranks)))
   :hints (("Goal"
            :induct (boymoo-compiler::index-lines lines defs index attachments sources packages entry target)
            :in-theory (disable assoc-equal boymoo-compiler::index-definition-line)))
   :rule-classes nil))

(defun assembly-definition-candidate-names (items)
  (if (atom items)
      nil
    (if (stringp (caar items))
        (cons (caar items) (assembly-definition-candidate-names (cdr items)))
      (assembly-definition-candidate-names (cdr items)))))

(defun assembly-program-candidate-names (lines)
  (if (atom lines)
      nil
    (append (and (equal (caar lines) "define") (assembly-definition-candidate-names (cddar lines)))
            (assembly-program-candidate-names (cdr lines)))))

(local
 (defthm assembly-candidate-append-is-string-list
   (implies (and (string-listp first) (string-listp rest))
            (string-listp (append first rest)))))

(local
 (defthm assembly-definition-names-are-strings
   (string-listp (assembly-definition-candidate-names items))))

(local
 (defthm assembly-program-names-are-strings
   (string-listp (assembly-program-candidate-names lines))))

(local
 (defthm assembly-candidate-deduplication-retains-members
   (iff (member-equal key (remove-duplicates-equal names))
        (member-equal key names))))

(local
 (defthm assembly-candidate-deduplication-removes-repeats
   (no-duplicatesp-equal (remove-duplicates-equal names))))

(local
 (defthm assembly-candidate-deduplication-retains-strings
   (implies (string-listp names)
            (string-listp (remove-duplicates-equal names)))))

(local
 (defthm assembly-string-list-is-label-key-list
   (implies (string-listp names)
            (assembly-label-key-list-p names))))

(local
 (defthm assembly-candidate-rank-entries-agree-with-membership
   (iff (assoc-equal key (assembly-key-rank-entries names universe))
        (member-equal key names))))

(local
 (defthm assembly-candidate-ranks-agree-with-membership
   (iff (assoc-equal key (assembly-key-ranks names))
        (member-equal key names))))

(local
 (defthm assembly-candidates-are-ranked
   (implies (subsetp-equal (assembly-definition-candidate-names items) names)
            (assembly-definition-candidates-ranked-p items (assembly-key-ranks names)))
   :hints (("Goal" :induct (len items) :in-theory (disable assembly-key-ranks)))))

(local
 (defthm assembly-subset-of-appended-names
   (equal (subsetp-equal (append first rest) names)
          (and (subsetp-equal first names) (subsetp-equal rest names)))))

(local
 (defthm assembly-program-candidates-are-ranked
   (implies (subsetp-equal (assembly-program-candidate-names lines) names)
            (assembly-program-candidates-ranked-p lines (assembly-key-ranks names)))
   :hints (("Goal" :induct (len lines) :in-theory (disable assembly-key-ranks
                                                        assembly-definition-candidate-names)))))

(local
 (defthm assembly-candidates-subset-of-deduplicated-list
   (equal (subsetp-equal names (remove-duplicates-equal universe))
          (subsetp-equal names universe))))

(local
 (defthm assembly-candidate-subset-allows-extra-name
   (implies (subsetp-equal names universe)
            (subsetp-equal names (cons extra universe)))
   :hints (("Goal" :induct (len names)))))

(defthm assembly-definition-name-subset-reflexive
  (subsetp-equal names names))

(local (in-theory (disable assembly-key-ranks assembly-program-candidate-names remove-duplicates-equal
                           boymoo-compiler::index-lines)))

(defthm assembly-index-lines-returns-distinct-definition-names
  (let ((defs (mv-nth 0 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
    (no-duplicatesp-equal (strip-cars defs)))
  :hints (("Goal"
           :use ((:instance assembly-index-lines-keep-definition-invariant
                            (defs nil) (index nil) (attachments nil) (sources nil)
                            (packages nil) (entry nil) (target nil)
                            (ranks (assembly-key-ranks
                                    (remove-duplicates-equal (assembly-program-candidate-names lines))))))
           :in-theory (enable assembly-index-definition-invariant-p)))
  :rule-classes nil)
