(in-package "BOYMOO")

(include-book "admit")
(include-book "guards-terms")

(verify-guards symbol-names
  :hints (("Goal" :in-theory (disable sym-name))))

(defthm cg-symbol-names-is-list
  (true-listp (symbol-names imports)))

(verify-guards declare-package
  :hints (("Goal" :in-theory (disable symbol-names import-trie trie-put))))
