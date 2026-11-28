(in-package "BOYMOO-PROOFS")

(include-book "value-allocation-trace")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::table-get boymoo-compiler::table-put boymoo-compiler::text-hash
                     boymoo-compiler::data-symbol boymoo-compiler::data-intern boymoo-compiler::data-bucket-add
                     boymoo-compiler::data-list-cells boymoo-compiler::data-text boymoo-compiler::data-vector
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                     boymoo-compiler::decode-part boymoo-compiler::declaration-list
                     data-symbol-allocation-trace data-intern-allocation-trace data-bucket-insertion-trace
                     data-list-cell-allocation-trace data-symbol-storage-input-p data-formals-storage-input-p
                     data-allocation-trace-block data-state-sized-p data-block-sized-p data-storable-table-p
                     boymoo-compiler::data-block boymoo-compiler::data-with-block length mv-nth)))

(local
 (defthm joined-package-traces-associate
   (equal (append (append first second) rest) (append first second rest))))

(local
 (defthm sized-state-has-a-word-offset
   (implies (data-state-sized-p state-data 80)
            (and (consp (boymoo-compiler::data-block state-data))
                 (natp (car (boymoo-compiler::data-block state-data)))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-state-sized-p data-block-sized-p)))))

(local
 (defthm sized-package-block-offset-is-an-integer
   (implies (data-block-sized-p block 80) (integerp (car block)))
   :hints (("Goal" :in-theory (enable data-block-sized-p)))))

(local
 (defthm block-replacement-sets-the-block-field
   (equal (boymoo-compiler::data-block (boymoo-compiler::data-with-block block state-data)) block)
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-block boymoo-compiler::data-with-block)))))

(local
 (defthm name-table-replacement-keeps-the-block-field
   (equal (boymoo-compiler::data-block (cons names (cdr state-data)))
          (boymoo-compiler::data-block state-data))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-block)))))

(local
 (defthm bucket-shape-survives-name-table-replacement
   (equal (data-state-buckets-p (cons names (cdr state-data))) (data-state-buckets-p state-data))))

(local
 (defthm trace-survives-name-table-replacement
   (equal (data-bucket-insertion-trace package name name-word symbol-word (cons names (cdr state-data)))
          (data-bucket-insertion-trace package name name-word symbol-word state-data))
   :hints (("Goal" :in-theory (enable data-bucket-insertion-trace)))))

(local
 (defthm import-name-lookup-has-a-word-chunk-tail
   (implies (data-state-sized-p state-data 80)
            (let ((entry (boymoo-compiler::table-get key hash 12 (car state-data))))
              (and (not (stringp entry)) (not (stringp (cdr entry))))))
   :hints (("Goal" :in-theory (enable data-storable-table-value-p)))))

(local
 (defthm import-bucket-trace-is-the-block-after-name-table-update
   (implies (and (data-state-sized-p state-data 80) (not (stringp name-word)) (not (stringp symbol-word)))
            (equal (boymoo-compiler::data-block
                    (boymoo-compiler::data-bucket-add number name name-word symbol-word (cons names (cdr state-data))))
                   (data-allocation-trace-block (data-bucket-insertion-trace number name name-word symbol-word state-data)
                                                (boymoo-compiler::data-block state-data))))
   :hints (("Goal" :use ((:instance data-bucket-insertion-trace-is-the-published-block
                                    (package number) (state-data (cons names (cdr state-data))))
                         (:instance data-sized-state-storage-components (start 80)))
                   :in-theory (disable data-state-buckets-p)))))

(local
 (defthm publishing-an-import-preserves-the-sized-state
   (implies (and (data-state-sized-p state-data 80)
                 (not (stringp name-word)) (not (stringp symbol-word)) (not (stringp entry)))
            (data-state-sized-p
             (boymoo-compiler::data-bucket-add number name name-word symbol-word
                                              (cons (boymoo-compiler::table-put
                                                     key (cons :import entry) hash 12 (car state-data))
                                                    (cdr state-data)))
             80))
   :hints (("Goal" :in-theory (enable data-storable-table-value-p)))))

(defun data-imports-allocation-trace (imports number packages common-lisp state-data reversed)
  (if (atom imports)
      (data-list-cell-allocation-trace reversed *proof-nil* (car (boymoo-compiler::data-block state-data)))
    (let ((text (car imports)))
      (mv-let (symbol-word named) (boymoo-compiler::data-symbol text packages state-data)
        (let* ((split (boymoo-compiler::symbol-separator text))
               (name (boymoo-compiler::decode-symbol-part text (+ 2 split) (length text)))
               (home (or (boymoo-compiler::index-get
                          (boymoo-compiler::decode-symbol-part text 0 split) packages) common-lisp))
               (entry (data-name-table-lookup home name named))
               (hash (+ (boymoo-compiler::text-hash name) (* 7919 number))))
          (append (data-symbol-allocation-trace text packages state-data)
                  (and (not (equal name "ACL2-PKG-WITNESS")) (not (data-name-table-lookup number name named))
                       (let ((next (boymoo-compiler::data-bucket-add
                                    number name (cdr entry) symbol-word
                                    (cons (boymoo-compiler::table-put (cons number name) (cons :import entry)
                                                                     hash 12 (car named))
                                          (cdr named)))))
                         (append (data-bucket-insertion-trace number name (cdr entry) symbol-word named)
                                 (data-imports-allocation-trace (cdr imports) number packages common-lisp
                                                                next (cons symbol-word reversed)))))))))))

(defthmd data-imports-allocation-trace-is-the-imports-block
  (implies (and (data-state-sized-p state-data 80) (data-formals-storage-input-p imports)
                (data-word-chunks-p reversed))
           (equal (boymoo-compiler::data-block (mv-nth 1 (boymoo-compiler::data-imports
                                                         imports number packages common-lisp state-data reversed)))
                  (data-allocation-trace-block (data-imports-allocation-trace
                                               imports number packages common-lisp state-data reversed)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :induct (data-imports-allocation-trace imports number packages common-lisp state-data reversed)
                  :in-theory (enable data-formals-storage-input-p data-symbol-allocation-trace-is-the-symbol-block
                                     data-list-cell-allocation-trace-is-the-list-block
                                     data-following-allocation-traces-appends-their-objects))))

(local
 (in-theory (disable boymoo-compiler::data-imports data-imports-allocation-trace)))

(defun data-package-declarations-allocation-trace (lines packages declared declarations state-data)
  (if (atom lines)
      nil
    (let* ((line (car lines)) (name (boymoo-compiler::decode-part (cadr line) 0 (length (cadr line))))
           (imports (caddr line)) (visible (equal (car line) "package"))
           (old (boymoo-compiler::index-get name declarations)))
      (cond ((and old (not (equal imports (car old)))) nil)
            (old (data-package-declarations-allocation-trace
                  (cdr lines) packages declared
                  (if visible (boymoo-compiler::index-set name (list imports (cadr old) t) declarations) declarations)
                  state-data))
            (t (let* ((number (boymoo-compiler::index-get name packages))
                      (items (boymoo-compiler::declaration-list imports))
                      (common-lisp (boymoo-compiler::index-get "COMMON-LISP" packages)))
                 (mv-let (imports-word next) (boymoo-compiler::data-imports items number declared common-lisp state-data nil)
                   (append (data-imports-allocation-trace items number declared common-lisp state-data nil)
                           (data-package-declarations-allocation-trace
                            (cdr lines) packages (boymoo-compiler::index-set name number declared)
                            (boymoo-compiler::index-set name (list imports imports-word visible) declarations) next)))))))))

(defthmd data-package-declarations-allocation-trace-is-the-declarations-block
  (implies (and (data-state-sized-p state-data 80) (data-package-lines-storage-input-p lines))
           (equal (boymoo-compiler::data-block (mv-nth 1 (boymoo-compiler::data-package-declarations
                                                         lines packages declared declarations state-data names)))
                  (data-allocation-trace-block (data-package-declarations-allocation-trace
                                               lines packages declared declarations state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-declarations lines packages declared declarations state-data names)
                  :in-theory (enable data-imports-allocation-trace-is-the-imports-block
                                     data-following-allocation-traces-appends-their-objects))))

(local
 (in-theory (disable boymoo-compiler::data-package-declarations data-package-declarations-allocation-trace
                     data-package-lines-storage-input-p boymoo-compiler::reverse-onto)))

(defun data-package-vectors-allocation-trace (names packages declarations state-data reversed)
  (if (atom names)
      (list (list* :header 6 (boymoo-compiler::reverse-onto reversed nil)))
    (let* ((name (car names)) (number (boymoo-compiler::index-get name packages))
           (declaration (boymoo-compiler::index-get name declarations)))
      (mv-let (name-word name-block) (boymoo-compiler::data-text 1 name (boymoo-compiler::data-block state-data))
        (let ((named (boymoo-compiler::data-with-block name-block state-data)))
          (mv-let (witness witness-name bound) (boymoo-compiler::data-intern number "ACL2-PKG-WITNESS" named)
            (declare (ignore witness-name))
            (let ((fields (list name-word (cadr declaration) (if (caddr declaration) witness *proof-nil*))))
              (mv-let (row row-block) (boymoo-compiler::data-vector fields (boymoo-compiler::data-block bound))
                (append (list (list :string name))
                        (data-intern-allocation-trace number "ACL2-PKG-WITNESS" named)
                        (list (list* :header 6 fields))
                        (data-package-vectors-allocation-trace
                         (cdr names) packages declarations (boymoo-compiler::data-with-block row-block bound)
                         (cons row reversed)))))))))))

(local
 (defthm reversing-a-list-onto-a-list-is-a-list
   (implies (true-listp tail) (true-listp (boymoo-compiler::reverse-onto list tail)))
   :hints (("Goal" :in-theory (enable boymoo-compiler::reverse-onto)))))

(local
 (defthm package-allocation-references-are-word-chunks
   (and (not (stringp (mv-nth 0 (boymoo-compiler::data-text 1 name block))))
        (not (stringp (mv-nth 0 (boymoo-compiler::data-vector fields block)))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-text boymoo-compiler::data-vector)))))

(local
 (defthm declaration-import-reference-is-a-word-chunk
   (implies (data-storable-table-p declarations 12 :declaration)
            (not (stringp (cadr (boymoo-compiler::index-get name declarations)))))
   :hints (("Goal" :use ((:instance data-index-get-returns-storable-value
                                    (text name) (index declarations) (kind :declaration)))
                   :in-theory (disable data-index-get-returns-storable-value)))))

(local
 (defthm named-package-state-is-sized
   (implies (and (data-state-sized-p state-data 80) (stringp name))
            (data-state-sized-p
             (boymoo-compiler::data-with-block (mv-nth 1 (boymoo-compiler::data-text
                                                         1 name (boymoo-compiler::data-block state-data)))
                                               state-data)
             80))))

(local
 (defthm vector-replacement-keeps-a-sized-state
   (implies (and (data-state-sized-p state-data 80) (data-word-chunks-p fields))
            (data-state-sized-p
             (boymoo-compiler::data-with-block (mv-nth 1 (boymoo-compiler::data-vector
                                                         fields (boymoo-compiler::data-block state-data)))
                                               state-data)
             80))))

(local
 (defthm package-witness-interning-gives-a-word-chunk
   (implies (data-state-sized-p state-data 80)
            (not (stringp (mv-nth 0 (boymoo-compiler::data-intern package "ACL2-PKG-WITNESS" state-data)))))
   :hints (("Goal" :use ((:instance data-intern-preserves-sized-state (start 80) (name "ACL2-PKG-WITNESS")))
                   :in-theory (disable data-intern-preserves-sized-state)))))

(local
 (defthm allocating-one-package-row-keeps-a-sized-state
   (mv-let (name-word name-block) (boymoo-compiler::data-text 1 name (boymoo-compiler::data-block state-data))
     (let* ((number (boymoo-compiler::index-get name packages))
            (declaration (boymoo-compiler::index-get name declarations))
            (named (boymoo-compiler::data-with-block name-block state-data)))
       (mv-let (witness witness-name bound) (boymoo-compiler::data-intern number "ACL2-PKG-WITNESS" named)
         (declare (ignore witness-name))
         (let ((fields (list name-word (cadr declaration) (if (caddr declaration) witness *proof-nil*))))
           (implies (and (data-state-sized-p state-data 80) (stringp name)
                         (data-storable-table-p declarations 12 :declaration))
                    (data-state-sized-p
                     (boymoo-compiler::data-with-block
                      (mv-nth 1 (boymoo-compiler::data-vector fields (boymoo-compiler::data-block bound))) bound)
                     80))))))
   :rule-classes nil))

(defthmd data-package-vectors-allocation-trace-is-the-vector-block
  (implies (and (data-state-sized-p state-data 80) (string-listp names)
                (data-storable-table-p declarations 12 :declaration) (data-word-chunks-p reversed))
           (equal (boymoo-compiler::data-block (mv-nth 1 (boymoo-compiler::data-package-vectors
                                                         names packages declarations state-data reversed)))
                  (data-allocation-trace-block (data-package-vectors-allocation-trace
                                               names packages declarations state-data reversed)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :induct (data-package-vectors-allocation-trace names packages declarations state-data reversed)
                  :in-theory (enable data-string-allocation-trace-is-the-text-block
                                     data-intern-allocation-trace-is-the-interned-block
                                     data-vector-allocation-trace-is-the-vector-block
                                     data-following-allocation-traces-appends-their-objects))
          ("Subgoal *1/2" :use ((:instance allocating-one-package-row-keeps-a-sized-state (name (car names)))))))

(local
 (in-theory (disable boymoo-compiler::data-package-vectors data-package-vectors-allocation-trace)))

(defun data-packages-allocation-trace (lines packages state-data reversed)
  (mv-let (decls next names) (boymoo-compiler::data-package-declarations lines packages nil nil state-data nil)
    (append (data-package-declarations-allocation-trace lines packages nil nil state-data)
            (data-package-vectors-allocation-trace names packages decls next reversed))))

(defthmd data-packages-allocation-trace-is-the-package-block
  (implies (and (data-state-sized-p state-data 80) (data-package-lines-storage-input-p lines) (data-word-chunks-p reversed))
           (equal (boymoo-compiler::data-block (mv-nth 1 (boymoo-compiler::data-packages
                                                         lines number packages state-data reversed)))
                  (data-allocation-trace-block (data-packages-allocation-trace lines packages state-data reversed)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :use ((:instance data-package-declarations-preserve-sized-state
                                   (declared nil) (declarations nil) (names nil) (start 80)))
                  :in-theory (enable data-package-declarations-allocation-trace-is-the-declarations-block
                                     data-package-vectors-allocation-trace-is-the-vector-block
                                     data-following-allocation-traces-appends-their-objects))))
