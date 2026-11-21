; Connect the reader's package index to the declarations that supply it.

(in-package "ACL2")

(include-book "round-trip")
(include-book "round-trip-lexical")

; A declaration lists its imports as symbols in the reader's form.
; Read a name from that form without consulting any package table.
(defun rt-import-name (symbol)
  (coerce (cadr (rt-reader-symbol-parts symbol)) 'list))

(defun rt-imports-name-p (name imports)
  (if (consp imports)
      (or (equal name (rt-import-name (car imports)))
          (rt-imports-name-p name (cdr imports)))
    nil))

(defun rt-declared-import-index (imports index)
  (if (consp imports)
      (rt-declared-import-index
       (cdr imports)
       (boymoo::trie-put (rt-import-name (car imports)) (list (car imports)) index))
    index))

(defun rt-declared-symbol-p (package name pkgs)
  (let ((record (boymoo::trie-get (coerce package 'list) pkgs)))
    (and record
         (not (rt-imports-name-p (coerce name 'list)
                                 (boymoo::prec-imports record))))))

(defun rt-package-index-of-its-imports-p (package pkgs)
  (let ((record (boymoo::trie-get (coerce package 'list) pkgs)))
    (equal (boymoo::prec-trie record)
           (rt-declared-import-index (boymoo::prec-imports record) nil))))

(defun rt-declarations-cover-written-symbols-p (x pkgs)
  (cond ((consp x)
         (and (rt-declarations-cover-written-symbols-p (car x) pkgs)
              (or (null (cdr x))
                  (rt-declarations-cover-written-symbols-p (cdr x) pkgs))))
        ((symbolp x)
         (let ((package (symbol-package-name x)))
           (and (rt-declared-symbol-p package (symbol-name x) pkgs)
                (rt-package-index-of-its-imports-p package pkgs))))
        (t t)))

; Inserting a key in the trie only changes the value at that key.
(local
 (defthm rt-trie-child-unchanged-after-dropping-other-child
   (implies (not (equal first other))
            (equal (boymoo::trie-child first (boymoo::trie-drop other kids))
                   (boymoo::trie-child first kids)))
   :hints (("Goal" :induct (boymoo::trie-drop other kids)))))

(local
 (defun rt-trie-keys-induction (key changed node)
   (if (and (consp key) (consp changed))
       (rt-trie-keys-induction (cdr key) (cdr changed)
                               (boymoo::trie-child (car key) (cdr node)))
     node)))

(local
 (defthm rt-trie-lookup-after-insertion
   (implies (and (true-listp key) (true-listp changed))
            (equal (boymoo::trie-get key (boymoo::trie-put changed value node))
                   (if (equal key changed) value (boymoo::trie-get key node))))
   :hints (("Goal" :induct (rt-trie-keys-induction key changed node)
            :do-not '(generalize fertilize)))))

(local
 (defthm rt-import-name-is-a-list
   (true-listp (rt-import-name symbol))
   :rule-classes :type-prescription))

(local
 (defthm rt-empty-trie-has-no-names
   (equal (boymoo::trie-get name nil) nil)))

(local
 (defthm rt-import-index-agrees-with-imports
   (implies (true-listp name)
            (iff (boymoo::trie-get name (rt-declared-import-index imports index))
                 (or (rt-imports-name-p name imports)
                     (boymoo::trie-get name index))))
   :hints (("Goal" :induct (rt-declared-import-index imports index)
            :in-theory (disable rt-import-name)))))

; A recorded import has a nonempty entry even when the symbol is NIL.
(defthm rt-package-index-agrees-with-declarations
  (implies (rt-package-index-of-its-imports-p package pkgs)
           (iff (rt-symbol-passes-index-p package name pkgs)
                (rt-declared-symbol-p package name pkgs)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance rt-import-index-agrees-with-imports
                                   (name (coerce name 'list)) (index nil)
                                   (imports (boymoo::prec-imports
                                             (boymoo::trie-get (coerce package 'list) pkgs)))))
           :in-theory (e/d (rt-symbol-passes-index-p)
                            (boymoo::trie-get rt-import-name
                             rt-import-index-agrees-with-imports)))))

(local
 (defthm rt-declared-symbol-passes-package-index
   (implies (and (rt-declared-symbol-p package name pkgs)
                 (rt-package-index-of-its-imports-p package pkgs))
            (rt-symbol-passes-index-p package name pkgs))
   :hints (("Goal" :use rt-package-index-agrees-with-declarations))))

(local
 (defthm rt-declarations-imply-index-checks
   (implies (rt-declarations-cover-written-symbols-p x pkgs)
            (rt-written-symbols-pass-index-p x pkgs))
   :hints (("Goal" :induct (rt-declarations-cover-written-symbols-p x pkgs)
            :in-theory (disable rt-declared-symbol-p rt-package-index-of-its-imports-p)))))

(defthm rt-parse-printed-line
  (implies (and (rt-word-p word)
                (rt-word-admitted-p word words)
                (true-listp args)
                (rt-format-datum-p args)
                (or (null args) (rt-declarations-cover-written-symbols-p args pkgs)))
           (equal (boymoo::parse-line
                   (append (coerce (bm-line word args) 'list) '(#\Newline))
                   words pkgs)
                  (cons (cdr (boymoo::pair-of (coerce word 'list) words))
                        (rt-datum-form args))))
  :rule-classes nil
  :hints (("Goal" :use rt-parse-printed-line-with-package-index
           :in-theory (disable boymoo::parse-line bm-line rt-word-p
                               rt-word-admitted-p boymoo::pair-of rt-datum-form))))
