(in-package "BOYMOO-PROOFS")

(include-book "label-order")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable assembly-text-number
                           boymoo-compiler::table-text-less)))

(defun assembly-label-key-p (key)
  (if (consp key)
      (and (assembly-label-key-p (car key))
           (assembly-label-key-p (cdr key)))
    (or (stringp key) (acl2-numberp key) (characterp key) (symbolp key))))

(local
 (defthm assembly-symbol-fields-identify-symbol
   (implies (and (symbolp a) (symbolp b))
            (equal (and (equal (symbol-name a) (symbol-name b))
                        (equal (symbol-package-name a) (symbol-package-name b)))
                   (equal a b)))
   :hints (("Goal"
            :use ((:instance acl2::intern-in-package-of-symbol-symbol-name
                             (acl2::x a) (acl2::y b))
                  (:instance acl2::intern-in-package-of-symbol-symbol-name
                             (acl2::x b) (acl2::y b)))
            :in-theory (disable acl2::intern-in-package-of-symbol-symbol-name)))))

(local
 (defthm assembly-code-identifies-character
   (implies (and (characterp a) (characterp b))
            (equal (equal (char-code a) (char-code b)) (equal a b)))
   :hints (("Goal"
            :use ((:instance acl2::code-char-char-code-is-identity (acl2::c a))
                  (:instance acl2::code-char-char-code-is-identity (acl2::c b)))
            :in-theory (disable acl2::code-char-char-code-is-identity)))))

(local
 (defthm assembly-complex-parts-identify-number
   (implies (and (acl2-numberp a) (acl2-numberp b))
            (equal (and (equal (realpart a) (realpart b))
                        (equal (imagpart a) (imagpart b)))
                   (equal a b)))
   :hints (("Goal"
            :use ((:instance acl2::realpart-imagpart-elim (acl2::x a))
                  (:instance acl2::realpart-imagpart-elim (acl2::x b)))
            :in-theory (disable acl2::realpart-imagpart-elim)))))

(local
 (defun assembly-key-primary (key)
   (case (boymoo-compiler::table-key-kind key)
     (0 (assembly-text-number key))
     (2 key)
     (3 (char-code key))
     (4 (assembly-text-number (symbol-name key)))
     (otherwise (realpart key)))))

(local
 (defun assembly-key-secondary (key)
   (case (boymoo-compiler::table-key-kind key)
     (4 (assembly-text-number (symbol-package-name key)))
     (5 (imagpart key))
     (otherwise 0))))

(local
 (defthm assembly-atom-key-numeric-order
   (implies (and (atom a) (atom b)
                 (equal (boymoo-compiler::table-key-kind a)
                        (boymoo-compiler::table-key-kind b)))
            (equal (boymoo-compiler::table-key-less a b)
                   (or (< (assembly-key-primary a) (assembly-key-primary b))
                       (and (equal (assembly-key-primary a) (assembly-key-primary b))
                            (< (assembly-key-secondary a) (assembly-key-secondary b))))))
   :hints (("Goal" :in-theory (enable assembly-text-number-injective)))
   :rule-classes nil))

(local
 (defthm assembly-atom-key-components-identify-key
   (implies (and (atom a) (atom b) (assembly-label-key-p a) (assembly-label-key-p b)
                 (equal (boymoo-compiler::table-key-kind a)
                        (boymoo-compiler::table-key-kind b)))
            (equal (and (equal (assembly-key-primary a) (assembly-key-primary b))
                        (equal (assembly-key-secondary a) (assembly-key-secondary b)))
                   (equal a b)))
   :hints (("Goal" :in-theory (enable assembly-text-number-injective)))
   :rule-classes nil))

(local
 (defthm assembly-key-primary-rational
   (rationalp (assembly-key-primary key))
   :rule-classes :type-prescription))

(local
 (defthm assembly-key-secondary-rational
   (rationalp (assembly-key-secondary key))
   :rule-classes :type-prescription))

(local
 (defthm assembly-key-order-by-kind
   (implies (not (equal (boymoo-compiler::table-key-kind a)
                        (boymoo-compiler::table-key-kind b)))
            (equal (boymoo-compiler::table-key-less a b)
                   (< (boymoo-compiler::table-key-kind a)
                      (boymoo-compiler::table-key-kind b))))))

(local
 (defthm assembly-key-order-of-conses
   (implies (and (consp a) (consp b))
            (equal (boymoo-compiler::table-key-less a b)
                   (if (equal (car a) (car b))
                       (boymoo-compiler::table-key-less (cdr a) (cdr b))
                     (boymoo-compiler::table-key-less (car a) (car b)))))))

(local
 (defthm assembly-atom-key-kind-is-not-one
   (implies (atom a)
            (not (equal (boymoo-compiler::table-key-kind a) 1)))))

(local
 (defthm assembly-key-kind-of-cons
   (implies (consp a)
            (equal (boymoo-compiler::table-key-kind a) 1))))

(local
 (defthm assembly-key-kind-rational
   (rationalp (boymoo-compiler::table-key-kind a))
   :rule-classes :type-prescription))

(local (in-theory (disable boymoo-compiler::table-key-less
                           boymoo-compiler::table-key-kind
                           assembly-key-primary assembly-key-secondary)))

(local
 (defthm assembly-atom-key-order
   (implies (and (atom a) (atom b) (assembly-label-key-p a) (assembly-label-key-p b))
            (and (equal (or (boymoo-compiler::table-key-less a b)
                            (boymoo-compiler::table-key-less b a))
                        (not (equal a b)))
                 (not (and (boymoo-compiler::table-key-less a b)
                           (boymoo-compiler::table-key-less b a)))))
   :hints (("Goal"
            :cases ((equal (boymoo-compiler::table-key-kind a)
                           (boymoo-compiler::table-key-kind b)))
            :use (assembly-atom-key-components-identify-key
                  assembly-atom-key-numeric-order
                  (:instance assembly-atom-key-numeric-order (a b) (b a)))))))

(local
 (defthm assembly-atom-key-order-transitive
   (implies (and (atom a) (atom b) (atom c)
                 (boymoo-compiler::table-key-less a b)
                 (boymoo-compiler::table-key-less b c))
            (boymoo-compiler::table-key-less a c))
   :hints (("Goal"
            :cases ((equal (boymoo-compiler::table-key-kind a)
                           (boymoo-compiler::table-key-kind b))
                    (equal (boymoo-compiler::table-key-kind b)
                           (boymoo-compiler::table-key-kind c)))
            :use (assembly-atom-key-numeric-order
                  (:instance assembly-atom-key-numeric-order (a b) (b c))
                  (:instance assembly-atom-key-numeric-order (a a) (b c)))))))

(local
 (defthm assembly-components-of-label-key
   (implies (and (consp key) (assembly-label-key-p key))
            (and (assembly-label-key-p (car key))
                 (assembly-label-key-p (cdr key))))
   :rule-classes :forward-chaining))

(local (in-theory (disable assembly-label-key-p)))

(local
 (defun assembly-key-pair-induction (a b)
   (if (and (consp a) (consp b))
       (list (assembly-key-pair-induction (car a) (car b))
             (assembly-key-pair-induction (cdr a) (cdr b)))
     (list a b))))

(defthm assembly-key-order-trichotomy
  (implies (and (assembly-label-key-p a) (assembly-label-key-p b))
           (and (equal (or (boymoo-compiler::table-key-less a b)
                           (boymoo-compiler::table-key-less b a))
                       (not (equal a b)))
                (not (and (boymoo-compiler::table-key-less a b)
                          (boymoo-compiler::table-key-less b a)))))
  :hints (("Goal" :induct (assembly-key-pair-induction a b))
          ("Subgoal *1/2" :cases ((consp a))
           :use assembly-atom-key-order))
  :rule-classes nil)

(defthm assembly-key-order-irreflexive
  (not (boymoo-compiler::table-key-less a a))
  :hints (("Goal" :induct (assembly-key-pair-induction a a))
          ("Subgoal *1/2"
           :use ((:instance assembly-atom-key-numeric-order (b a))))))

(local
 (defun assembly-key-triple-induction (a b c)
   (if (and (consp a) (consp b) (consp c))
       (list (assembly-key-triple-induction (car a) (car b) (car c))
             (assembly-key-triple-induction (cdr a) (cdr b) (cdr c)))
     (list a b c))))

(local
 (defthm assembly-key-order-increases-kind
   (implies (boymoo-compiler::table-key-less a b)
            (<= (boymoo-compiler::table-key-kind a)
                (boymoo-compiler::table-key-kind b)))
   :hints (("Goal" :cases ((equal (boymoo-compiler::table-key-kind a)
                                 (boymoo-compiler::table-key-kind b)))))
   :rule-classes nil))

(defthm assembly-key-order-transitive
  (implies (and (boymoo-compiler::table-key-less a b)
                (boymoo-compiler::table-key-less b c))
           (boymoo-compiler::table-key-less a c))
  :hints (("Goal" :induct (assembly-key-triple-induction a b c))
          ("Subgoal *1/2"
           :use (assembly-atom-key-order-transitive
                 assembly-key-order-increases-kind
                 (:instance assembly-key-order-increases-kind (a b) (b c)))
           :cases ((consp a) (consp b) (consp c)
                   (equal (boymoo-compiler::table-key-kind a)
                          (boymoo-compiler::table-key-kind c)))))
  :rule-classes nil)

(defun assembly-label-key-list-p (keys)
  (if (atom keys)
      (null keys)
    (and (assembly-label-key-p (car keys))
         (assembly-label-key-list-p (cdr keys)))))

(defun assembly-smaller-key-count (key keys)
  (if (atom keys)
      0
    (+ (if (boymoo-compiler::table-key-less (car keys) key) 1 0)
       (assembly-smaller-key-count key (cdr keys)))))

(local
 (defthm assembly-smaller-key-count-increases
   (implies (boymoo-compiler::table-key-less a b)
            (and (<= (assembly-smaller-key-count a keys) (assembly-smaller-key-count b keys))
                 (implies (member-equal a keys)
                          (< (assembly-smaller-key-count a keys)
                             (assembly-smaller-key-count b keys)))))
   :hints (("Goal" :induct (assembly-smaller-key-count a keys))
           ("Subgoal *1/2"
            :use ((:instance assembly-key-order-transitive (a (car keys)) (b a) (c b)))))
   :rule-classes nil))

(local
 (defthm assembly-smaller-key-count-orders-keys
   (implies (and (assembly-label-key-p a) (assembly-label-key-p b)
                 (member-equal a keys) (member-equal b keys))
            (and (equal (< (assembly-smaller-key-count a keys)
                           (assembly-smaller-key-count b keys))
                        (boymoo-compiler::table-key-less a b))
                 (equal (equal (assembly-smaller-key-count a keys)
                               (assembly-smaller-key-count b keys))
                        (equal a b))))
   :hints (("Goal" :use (assembly-key-order-trichotomy
                        assembly-smaller-key-count-increases
                        (:instance assembly-smaller-key-count-increases (a b) (b a)))
                   :in-theory (disable assembly-smaller-key-count)))
   :rule-classes nil))

(defun assembly-key-rank-entries (keys universe)
  (if (atom keys)
      nil
    (acons (car keys) (assembly-smaller-key-count (car keys) universe)
           (assembly-key-rank-entries (cdr keys) universe))))

(defun assembly-key-ranks (keys)
  (assembly-key-rank-entries keys keys))

(local (in-theory (disable assembly-smaller-key-count)))

(local
 (defthm assembly-ranked-pair-from-key-counts
   (implies (and (assembly-label-key-p a) (assembly-label-key-p b)
                 (member-equal a universe) (member-equal b universe)
                 (not (equal a b)))
            (assembly-ranked-pair-p
             (cons a (assembly-smaller-key-count a universe))
             (cons b (assembly-smaller-key-count b universe))))
   :hints (("Goal" :use ((:instance assembly-smaller-key-count-orders-keys (keys universe))
                        (:instance assembly-smaller-key-count-orders-keys
                                   (keys universe) (a b) (b a)))))))

(local
 (defthm assembly-ranked-against-other-key-counts
   (implies (and (assembly-label-key-p key) (assembly-label-key-list-p keys)
                 (member-equal key universe) (subsetp-equal keys universe)
                 (not (member-equal key keys)))
            (assembly-ranked-against-p
             (cons key (assembly-smaller-key-count key universe))
             (assembly-key-rank-entries keys universe)))
   :hints (("Goal" :induct (assembly-key-rank-entries keys universe)
                   :in-theory (disable assembly-ranked-pair-p)))))

(local
 (defthm assembly-ranking-p-of-key-rank-entries
   (implies (and (assembly-label-key-list-p keys) (no-duplicatesp-equal keys)
                 (subsetp-equal keys universe))
            (assembly-ranking-p (assembly-key-rank-entries keys universe)))
   :hints (("Goal" :induct (assembly-key-rank-entries keys universe)
                   :in-theory (disable assembly-ranked-against-p)))))

(local (in-theory (enable assembly-subset-of-self assembly-subset-survives-cons)))

(defthm assembly-key-ranks-pass-check
  (implies (and (assembly-label-key-list-p keys) (no-duplicatesp-equal keys))
           (assembly-ranking-p (assembly-key-ranks keys))))

(local
 (defthm assembly-key-rank-association
   (iff (assoc-equal key (assembly-key-rank-entries keys universe))
        (member-equal key keys))))

(local
 (defthm assembly-key-ranks-cover-entries
   (implies (subsetp-equal (assembly-keys entries) keys)
            (assembly-ranked-entries-p entries (assembly-key-rank-entries keys universe)))
   :hints (("Goal" :induct (len entries)))))

(local
 (defthm assembly-empty-label-table-is-available
   (and (assembly-labels-unused-p entries nil)
        (assembly-table-p bits nil ranks))
   :hints (("Goal" :induct (assembly-labels-unused-p entries nil)
                   :in-theory (disable boymoo-compiler::label-hash)))))

(defthm assembly-layout-input-with-key-ranks
  (let ((item-keys (assembly-keys (assembly-labels items pc))))
    (implies (and (natp pc) (assembly-layout-sizes-p items)
                  (no-duplicatesp-equal item-keys)
                  (assembly-label-key-list-p keys) (no-duplicatesp-equal keys)
                  (subsetp-equal item-keys keys))
             (assembly-layout-input-p items pc nil (assembly-key-ranks keys))))
  :hints (("Goal" :in-theory (disable assembly-labels assembly-labels-unused-p
                                      assembly-ranking-p assembly-ranked-entries-p
                                      assembly-table-p))))

(defthm assembly-layout-input-for-distinct-labels
  (let ((keys (assembly-keys (assembly-labels items pc))))
    (implies (and (natp pc)
                  (assembly-layout-sizes-p items)
                  (assembly-label-key-list-p keys)
                  (no-duplicatesp-equal keys))
             (assembly-layout-input-p items pc nil (assembly-key-ranks keys))))
  :hints (("Goal" :use ((:instance assembly-layout-input-with-key-ranks
                                   (keys (assembly-keys (assembly-labels items pc)))))
                  :in-theory (disable assembly-labels assembly-layout-input-p
                                      assembly-layout-input-with-key-ranks))))

(local
 (defthm assembly-key-ranks-cover-key
   (iff (assoc-equal query (assembly-key-ranks keys))
        (member-equal query keys))))

(local
 (defthm assembly-keys-subset-with-addition
   (subsetp-equal keys (add-to-set-equal query keys))
   :hints (("Goal" :expand ((add-to-set-equal query keys))))))

(defthm assembly-layout-lookup-from-empty
  (let ((entries (assembly-labels items pc)))
    (implies (and (natp pc)
                  (assembly-layout-sizes-p items)
                  (assembly-label-key-p query)
                  (assembly-label-key-list-p (assembly-keys entries))
                  (no-duplicatesp-equal (assembly-keys entries)))
             (equal (boymoo-compiler::table-get
                     query (boymoo-compiler::label-hash query) 16
                     (mv-nth 1 (boymoo-compiler::a64-layout items pc nil rest)))
                    (cdr (assoc-equal query entries)))))
  :hints (("Goal"
           :use ((:instance assembly-layout-input-with-key-ranks
                            (keys (add-to-set-equal query (assembly-keys (assembly-labels items pc)))))
                 (:instance assembly-layout-label-lookup
                            (table nil)
                            (ranks (assembly-key-ranks
                                    (add-to-set-equal query (assembly-keys (assembly-labels items pc)))))))
           :in-theory (disable assembly-layout-input-with-key-ranks
                               assembly-layout-label-lookup
                               assembly-layout-input-p assembly-labels boymoo-compiler::a64-layout
                               assembly-key-ranks boymoo-compiler::label-hash))))
