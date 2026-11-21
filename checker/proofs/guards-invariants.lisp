(in-package "BOYMOO")

(include-book "guards-check")

; A clause carries one natural size for each literal. A world may also
; hold a name with no associated clause.
; A table records a different kind of value according to its use. NIL
; denotes absence at any node. Children have character keys.
(defthm cg-trie-child-keeps-trie
  (implies (guard-trie-kids-p kids kind)
           (guard-trie-p (trie-child c kids) kind))
  :hints (("Goal" :induct (trie-child c kids))))

(defthm cg-trie-drop-keeps-kids
  (implies (guard-trie-kids-p kids kind)
           (guard-trie-kids-p (trie-drop c kids) kind))
  :hints (("Goal" :induct (trie-drop c kids))))

(defthm cg-trie-get-keeps-value
  (implies (guard-trie-p node kind)
           (guard-trie-value-p (trie-get key node) kind))
  :hints (("Goal" :induct (trie-get key node)
           :in-theory (disable trie-child))))

(defthm cg-trie-put-keeps-trie
  (implies (and (character-listp key)
                (guard-trie-value-p value kind)
                (guard-trie-p node kind))
           (guard-trie-p (trie-put key value node) kind))
  :hints (("Goal" :induct (trie-put key value node)
           :in-theory (disable trie-child trie-drop))))

(defthm cg-sum-of-naturals
  (implies (guard-natural-list-p xs)
           (natp (sum xs)))
  :hints (("Goal" :induct (sum xs))))

(defthm cg-sizes-are-naturals
  (guard-natural-list-p (sizes xs))
  :hints (("Goal" :induct (sizes xs) :in-theory (disable size))))

(defthm cg-length-of-sizes
  (equal (len (sizes xs)) (len xs))
  :hints (("Goal" :induct (sizes xs) :in-theory (disable size))))

(defthm cg-sized-clause-with-sizes
  (implies (true-listp lits)
           (guard-sized-clause-p (cons lits (sizes lits)))))

(defthm cg-unit-fact-is-sized-clause
  (guard-sized-clause-p (unit-fact term))
  :hints (("Goal" :in-theory (disable size))))

(defthm cg-bump-keeps-naturals
  (implies (guard-natural-list-p counts)
           (guard-natural-list-p (bump i counts)))
  :hints (("Goal" :induct (bump i counts))))

(defthm cg-bump-keeps-length
  (equal (len (bump i counts)) (len counts))
  :hints (("Goal" :induct (bump i counts))))

(local
 (in-theory (disable trie-put trie-get sym-text symbol-names sym-name size bump)))

(defthm cg-count-one-keeps-world
  (implies (guard-world-p w)
           (guard-world-p (count-one i w))))

(defthm cg-put-entry-keeps-world
  (implies (and (guard-world-p w)
                (guard-name-record-p entry))
           (guard-world-p (put-entry name entry w))))

(defthm cg-set-string-facts-keeps-world
  (implies (and (guard-world-p w) (guard-string-facts-p entries))
           (guard-world-p (set-sfacts entries w))))

(defthm cg-string-facts-of-world
  (implies (guard-world-p w)
           (guard-string-facts-p (w-sfacts w))))

(defthm cg-set-specials-keeps-world
  (implies (and (guard-world-p w) (guard-trie-p specials :special))
           (guard-world-p (set-specials specials w))))

(defthm cg-set-acl2-keeps-world
  (implies (and (guard-world-p w) (guard-trie-p imports :import))
           (guard-world-p (set-acl2 imports w))))

(defthm cg-symbol-names-are-character-lists
  (guard-character-lists-p (symbol-names xs))
  :hints (("Goal" :induct (symbol-names xs)
           :in-theory (enable symbol-names))))

(defthm cg-import-trie-keeps-trie
  (implies (and (symbol-listp imports)
                (guard-character-lists-p names)
                (guard-trie-p node :import))
           (guard-trie-p (import-trie imports names node) :import))
  :hints (("Goal" :induct (import-trie imports names node))))

(defthm cg-declare-package-keeps-world
  (implies (and (guard-world-p w)
                (character-listp name)
                (symbol-listp imports)
                (booleanp hidden)
                (true-listp lines))
           (guard-world-p (declare-package name imports hidden lines w)))
  :hints (("Goal" :in-theory (disable import-trie))))

(defthm cg-specials-trie-keeps-trie
  (implies (guard-trie-p node :special)
           (guard-trie-p (specials-trie names node) :special))
  :hints (("Goal" :induct (specials-trie names node))))

(defthm cg-initial-world
  (guard-world-p (initial-world))
  :hints (("Goal" :in-theory (disable declare-package put-entry))))

(defthm cg-package-record-of-lookup
  (implies (guard-trie-p node :package)
           (let ((rec (trie-get key node)))
             (and (true-listp rec)
                  (guard-trie-p (prec-trie rec) :import))))
  :hints (("Goal" :use ((:instance cg-trie-get-keeps-value (kind :package)))
           :expand ((guard-trie-value-p (trie-get key node) :package))
           :in-theory (disable cg-trie-get-keeps-value))))

(defthm cg-import-of-lookup
  (implies (guard-trie-p node :import)
           (let ((found (trie-get key node)))
             (or (not found)
                 (and (consp found) (symbolp (car found))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance cg-trie-get-keeps-value (kind :import)))
           :expand ((guard-trie-value-p (trie-get key node) :import))
           :in-theory (disable cg-trie-get-keeps-value))))

(defthm cg-ground-line-keeps-world
  (implies (and (guard-world-p w) (guard-ground-line-p line))
           (guard-world-p (ground-line line w)))
  :hints (("Goal" :in-theory (disable declare-package put-entry count-one
                                     package-rule-name unit-fact guard-sized-clause-p
                                     specials-trie import-trie set-specials set-acl2
                                     set-sfacts guard-world-p))))
