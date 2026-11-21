; Recover native ACL2 data from an accepted line.

(in-package "ACL2")

(include-book "round-trip-converse")
(include-book "round-trip-packages")

; A native name is available when interning with the package witness
; gives a symbol whose home package is the requested package.
(defund rt-native-symbol (package name)
  (intern-in-package-of-symbol name (pkg-witness package)))

(defund rt-native-name-p (package name)
  (and (stringp package) (not (equal package "")) (stringp name)
       (equal (symbol-package-name (rt-native-symbol package name)) package)))

(defun rt-native-names-p (x)
  (cond ((consp x)
         (and (rt-native-names-p (car x)) (rt-native-names-p (cdr x))))
        ((and (symbolp x) x (not (equal x t)))
         (let ((parts (rt-reader-symbol-parts x)))
           (rt-native-name-p (car parts) (cadr parts))))
        (t t)))

(defun rt-native-datum (x)
  (cond ((consp x)
         (cons (rt-native-datum (car x)) (rt-native-datum (cdr x))))
        ((and (symbolp x) x (not (equal x t)))
         (let ((parts (rt-reader-symbol-parts x)))
           (rt-native-symbol (car parts) (cadr parts))))
        (t x)))

; Interning gives a symbol with the given name. Knowing its home
; package determines both the native datum and its reader form.
(local
 (defthm rt-resolved-name-is-symbol
   (symbolp (rt-native-symbol package name))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable rt-native-symbol)))))

(local
 (defthm rt-resolved-symbol-has-name
   (implies (stringp name)
            (equal (symbol-name (rt-native-symbol package name)) name))
   :hints (("Goal" :in-theory (enable rt-native-symbol)))))

(local
 (defthm rt-native-symbol-for-available-name
   (implies (and (rt-native-name-p package name)
                 (rt-symbol-passes-index-p package name pkgs))
            (let ((symbol (rt-native-symbol package name)))
              (and (rt-format-datum-p symbol)
                   (equal (rt-datum-form symbol) (rt-reader-symbol package name))
                   (rt-written-symbols-pass-index-p symbol pkgs))))
   :hints (("Goal" :in-theory (enable rt-native-name-p)
            :expand ((rt-datum-form (rt-native-symbol package name))
                     (rt-format-datum-p (rt-native-symbol package name))
                     (rt-written-symbols-pass-index-p
                      (rt-native-symbol package name) pkgs))))))

(defthm rt-native-datum-has-its-reader-form
  (implies (and (rt-reader-datum-in-table-p x pkgs) (rt-native-names-p x))
           (and (rt-format-datum-p (rt-native-datum x))
                (equal (rt-datum-form (rt-native-datum x)) x)
                (rt-written-symbols-pass-index-p (rt-native-datum x) pkgs)))
  :rule-classes nil
  :hints (("Goal" :induct (rt-native-datum x)
           :in-theory (enable rt-reader-atom-in-table-p rt-native-name-p))))

; Every native datum has available names in its reader form, and
; recovering those names inverts the encoding.
(local
 (defthm rt-resolution-of-native-symbol
   (implies (and (symbolp x) (not (equal (symbol-package-name x) "")))
            (equal (rt-native-symbol (symbol-package-name x) (symbol-name x)) x))
   :hints (("Goal"
            :use ((:instance intern-in-package-of-symbol-symbol-name
                             (y (pkg-witness (symbol-package-name x)))))
            :in-theory (e/d (rt-native-symbol)
                             (intern-in-package-of-symbol-symbol-name))))))

(local
 (defthm rt-native-name-p-of-a-native-symbol
   (implies (and (symbolp x) (not (equal (symbol-package-name x) "")))
            (rt-native-name-p (symbol-package-name x) (symbol-name x)))
   :hints (("Goal" :in-theory (enable rt-native-name-p)))))

(local
 (defthm rt-native-atom-of-datum-form
   (implies (and (rt-format-datum-p x) (not (consp x)))
            (and (rt-native-names-p (rt-datum-form x))
                 (equal (rt-native-datum (rt-datum-form x)) x)))
   :hints (("Goal"
            :use ((:instance rt-datum-form-injective (y nil))
                  (:instance rt-datum-form-injective (y t)))
            :in-theory (disable rt-datum-form-injective)
            :expand ((rt-datum-form x))
            :do-not-induct t))))

(defthm rt-native-datum-inverts-datum-form
  (implies (rt-format-datum-p x)
           (and (rt-native-names-p (rt-datum-form x))
                (equal (rt-native-datum (rt-datum-form x)) x)))
  :rule-classes nil
  :hints (("Goal" :induct (rt-datum-form x)
           :in-theory (disable (:definition rt-datum-form)))))

(local
 (defthm rt-native-datum-of-true-list
   (implies (true-listp xs)
            (true-listp (rt-native-datum xs)))))

; Every accepted argument has a native datum if its names are
; available. The printer can be applied to this recovered list.
(defthm rt-accepted-line-with-native-names-is-printer-text
  (let* ((read (boymoo::parse-line cs words pkgs))
         (args (rt-native-datum (cdr read)))
         (word (rt-line-word cs)))
    (implies (and read (rt-word-p word)
                  (rt-native-names-p (cdr read)))
             (and (true-listp args)
                  (rt-format-datum-p args)
                  (equal (rt-datum-form args) (cdr read))
                  (equal cs (append (coerce (bm-line word args) 'list)
                                    '(#\Newline))))))
  :rule-classes nil
  :hints (("Goal"
           :use (rt-accepted-arguments-are-in-table
                 (:instance rt-native-datum-has-its-reader-form
                            (x (cdr (boymoo::parse-line cs words pkgs))))
                 (:instance rt-accepted-line-is-printer-text
                            (args (rt-native-datum (cdr (boymoo::parse-line cs words pkgs))))))
           :in-theory (disable boymoo::parse-line boymoo::pair-of rt-word-p
                               bm-line rt-line-word rt-native-datum
                               rt-native-names-p rt-datum-form rt-format-datum-p))))

; A compatible declaration indexes its own imports and excludes every
; name that ACL2 imports into the package. Extra declared imports do
; not affect recovery of the names the reader accepts.
(defun rt-covers-native-import-names-p (native-imports index)
  (if (consp native-imports)
      (and (boymoo::trie-get (coerce (symbol-name (car native-imports)) 'list) index)
           (rt-covers-native-import-names-p (cdr native-imports) index))
    t))

(defun rt-compatible-package-record-p (package record)
  (and (not (equal package ""))
       (equal (boymoo::prec-trie record)
              (rt-declared-import-index (boymoo::prec-imports record) nil))
       (rt-covers-native-import-names-p (pkg-imports package)
                                       (boymoo::prec-trie record))))

; Traverse the package trie, accumulating the reversed key to each
; record. Each record supplies the conditions needed at that package.
(mutual-recursion
 (defun rt-compatible-package-node-p (node reversed-key)
   (if (consp node)
       (and (or (null (car node))
                (rt-compatible-package-record-p
                 (coerce (revappend reversed-key nil) 'string) (car node)))
            (rt-compatible-package-children-p (cdr node) reversed-key))
     t))
 (defun rt-compatible-package-children-p (children reversed-key)
   (if (consp children)
       (and (or (not (consp (car children)))
                (rt-compatible-package-node-p (cdar children)
                                              (cons (caar children) reversed-key)))
            (rt-compatible-package-children-p (cdr children) reversed-key))
     t)))

(defun rt-compatible-package-table-p (pkgs)
  (rt-compatible-package-node-p pkgs nil))

(local
 (defthm rt-compatible-package-child
   (implies (rt-compatible-package-children-p children reversed-key)
            (rt-compatible-package-node-p (boymoo::trie-child c children)
                                          (cons c reversed-key)))
   :hints (("Goal" :induct (boymoo::trie-child c children)
            :in-theory (disable rt-compatible-package-record-p)))))

(local
 (defun rt-package-lookup-induction (key node reversed-key)
   (if (and (consp key) (consp node))
       (rt-package-lookup-induction (cdr key)
                                    (boymoo::trie-child (car key) (cdr node))
                                    (cons (car key) reversed-key))
     reversed-key)))

(local
 (defthm rt-found-package-record-is-compatible
   (implies (and (true-listp key)
                 (rt-compatible-package-node-p node reversed-key)
                 (boymoo::trie-get key node))
            (rt-compatible-package-record-p
             (coerce (revappend reversed-key key) 'string)
             (boymoo::trie-get key node)))
   :hints (("Goal" :induct (rt-package-lookup-induction key node reversed-key)
            :in-theory (disable rt-compatible-package-record-p
                                rt-compatible-package-children-p)
            :expand ((rt-compatible-package-node-p node reversed-key))))))

(local
 (defthm rt-lookup-in-compatible-package-table
   (implies (and (stringp package) (rt-compatible-package-table-p pkgs)
                 (boymoo::trie-get (coerce package 'list) pkgs))
            (rt-compatible-package-record-p
             package (boymoo::trie-get (coerce package 'list) pkgs)))
   :hints (("Goal" :use ((:instance rt-found-package-record-is-compatible
                                   (key (coerce package 'list))
                                   (node pkgs) (reversed-key nil)))
            :in-theory (disable boymoo::trie-get rt-compatible-package-node-p
                                rt-compatible-package-record-p
                                rt-found-package-record-is-compatible)))))

; An owned name in a compatible record is absent from ACL2's imports.
(local
 (defthm rt-covered-import-has-index-entry
   (implies (and (rt-covers-native-import-names-p native-imports index)
                 (member-symbol-name name native-imports))
            (boymoo::trie-get (coerce name 'list) index))
   :hints (("Goal" :induct (rt-covers-native-import-names-p native-imports index)
            :in-theory (e/d (member-symbol-name) (boymoo::trie-get))))))

(local
 (defthm rt-compatible-record-permits-native-name
   (implies (and (stringp package) (stringp name)
                 (rt-compatible-package-record-p package record)
                 (not (boymoo::trie-get (coerce name 'list) (boymoo::prec-trie record))))
            (rt-native-name-p package name))
   :hints (("Goal"
            :use ((:instance rt-covered-import-has-index-entry
                             (native-imports (pkg-imports package))
                             (index (boymoo::prec-trie record)))
                  (:instance symbol-package-name-intern-in-package-of-symbol
                             (x name) (y (pkg-witness package))))
            :in-theory (e/d (rt-native-name-p rt-native-symbol)
                             (boymoo::trie-get rt-covered-import-has-index-entry
                              symbol-package-name-intern-in-package-of-symbol))))))

(local
 (defthm rt-declared-symbol-in-compatible-table
   (implies (and (stringp package) (rt-compatible-package-table-p pkgs)
                 (rt-symbol-passes-index-p package name pkgs))
            (and (rt-declared-symbol-p package name pkgs)
                 (rt-package-index-of-its-imports-p package pkgs)))
   :hints (("Goal" :use (rt-package-index-agrees-with-declarations
                         rt-lookup-in-compatible-package-table)
            :in-theory (e/d (rt-symbol-passes-index-p)
                             (boymoo::trie-get rt-compatible-package-table-p
                              rt-compatible-package-node-p
                              rt-lookup-in-compatible-package-table))))))

(local
 (defthm rt-native-name-in-compatible-table
   (implies (and (stringp package) (stringp name) (rt-compatible-package-table-p pkgs)
                 (rt-symbol-passes-index-p package name pkgs))
            (rt-native-name-p package name))
   :hints (("Goal"
            :use (rt-lookup-in-compatible-package-table
                  (:instance rt-compatible-record-permits-native-name
                             (record (boymoo::trie-get (coerce package 'list) pkgs))))
            :in-theory (e/d (rt-symbol-passes-index-p)
                             (boymoo::trie-get rt-compatible-package-table-p
                              rt-compatible-package-record-p
                              rt-lookup-in-compatible-package-table
                              rt-compatible-record-permits-native-name))))))

(local
 (defthm rt-compatible-table-supplies-native-names
   (implies (and (rt-compatible-package-table-p pkgs)
                 (rt-reader-datum-in-table-p x pkgs))
            (rt-native-names-p x))
   :hints (("Goal" :induct (rt-reader-datum-in-table-p x pkgs)
            :in-theory (e/d (rt-reader-atom-in-table-p)
                             (rt-compatible-package-table-p))))))

(local
 (defthm rt-compatible-table-declares-native-data
   (implies (and (rt-compatible-package-table-p pkgs)
                 (rt-written-symbols-pass-index-p x pkgs))
            (rt-declarations-cover-written-symbols-p x pkgs))
   :hints (("Goal" :induct (rt-written-symbols-pass-index-p x pkgs)
            :in-theory (disable rt-compatible-package-table-p
                                rt-declared-symbol-p rt-package-index-of-its-imports-p)))))

(defthm rt-accepted-line-with-compatible-packages-is-printer-text
  (let* ((read (boymoo::parse-line cs words pkgs))
         (args (rt-native-datum (cdr read)))
         (word (rt-line-word cs)))
    (implies (and read (not (boymoo::pair-of nil words))
                  (rt-compatible-package-table-p pkgs))
             (and (rt-word-p word)
                  (true-listp args)
                  (rt-format-datum-p args)
                  (or (null args) (rt-declarations-cover-written-symbols-p args pkgs))
                  (equal (rt-datum-form args) (cdr read))
                  (equal cs (append (coerce (bm-line word args) 'list)
                                    '(#\Newline))))))
  :rule-classes nil
  :hints (("Goal"
           :use (rt-accepted-line-has-format-word
                 rt-accepted-arguments-are-in-table
                 rt-accepted-line-with-native-names-is-printer-text
                 (:instance rt-compatible-table-supplies-native-names
                            (x (cdr (boymoo::parse-line cs words pkgs))))
                 (:instance rt-native-datum-has-its-reader-form
                            (x (cdr (boymoo::parse-line cs words pkgs)))))
           :in-theory (disable boymoo::parse-line boymoo::pair-of rt-word-p
                               bm-line rt-line-word rt-native-datum rt-native-names-p
                               rt-datum-form rt-format-datum-p
                               rt-declarations-cover-written-symbols-p
                               rt-compatible-package-table-p
                               rt-compatible-table-supplies-native-names))))

; A package index can agree with its declaration while that package's
; native ACL2 imports disallow a name that the declaration allows.
(defthm rt-conflicting-native-import-is-read
  (let* ((pkgs (boymoo::trie-put (coerce "BOYMOO" 'list) (list nil nil nil nil) nil))
         (words (list (cons (coerce "reserve" 'list) :reserve)))
         (line (append (coerce "(reserve BOYMOO::CAR)" 'list) '(#\Newline))))
    (and (rt-package-index-of-its-imports-p "BOYMOO" pkgs)
         (rt-declared-symbol-p "BOYMOO" "CAR" pkgs)
         (equal (boymoo::parse-line line words pkgs) '(:reserve boymoo::|BOYMOO::CAR|))
         (not (rt-native-names-p '(boymoo::|BOYMOO::CAR|)))))
  :rule-classes nil)

(defthm rt-conflicting-native-import-has-no-preimage
  (implies (rt-format-datum-p x)
           (not (equal (rt-datum-form x) '(boymoo::|BOYMOO::CAR|))))
  :rule-classes nil
  :hints (("Goal" :use rt-native-datum-inverts-datum-form
           :in-theory (disable rt-native-datum rt-native-names-p rt-datum-form))))
