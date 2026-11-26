(in-package "BOYMOO-PROOFS")

(include-book "packages")
(include-book "buckets")

(logic)
(set-verify-guards-eagerness 0)

(defthmd data-vector-allocates-header-and-fields
  (implies (and (integerp (car block)) (true-listp words))
           (equal (mv-list 2 (boymoo-compiler::data-vector words block))
                  (list (+ (car block) 2)
                        (cons (+ (car block) 8 (* 8 (len words)))
                              (boymoo-compiler::reverse-onto
                               words (cons (+ 6 (* 2048 (len words))) (cdr block)))))))
  :hints (("Goal" :in-theory (e/d (data-ash-left data-words-allocate-consecutively)
                                 (boymoo-compiler::data-words ash)))))

(local
 (in-theory (disable boymoo-compiler::data-symbol boymoo-compiler::decode-symbol-part
                     boymoo-compiler::symbol-separator boymoo-compiler::index-get
                     boymoo-compiler::table-get boymoo-compiler::table-put
                     boymoo-compiler::text-hash data-table-p)))

(defthmd data-single-import-installs-name-and-bucket
  (mv-let (symbol-word named) (boymoo-compiler::data-symbol text packages state-data)
    (let* ((split (boymoo-compiler::symbol-separator text))
           (name (boymoo-compiler::decode-symbol-part text (+ 2 split) (length text)))
           (home (or (boymoo-compiler::index-get
                      (boymoo-compiler::decode-symbol-part text 0 split) packages)
                     common-lisp))
           (home-binding (data-name-table-lookup home name named))
           (offset (car (boymoo-compiler::data-block named))))
      (implies (and (natp package) (stringp name) (not (equal name "ACL2-PKG-WITNESS"))
                    (data-table-p (car named) 12) (natp offset)
                    (equal (car home-binding) symbol-word) (consp home-binding)
                    (not (data-name-table-lookup package name named)))
               (mv-let (imports-word next) (boymoo-compiler::data-imports
                                           (list text) package packages common-lisp state-data nil)
                 (and (equal (data-name-table-lookup package name next) (cons :import home-binding))
                      (equal (caddr next)
                             (boymoo-compiler::bucket-set
                              (data-bucket-for-name package name) 12 (+ 32 offset) (caddr named)))
                      (equal imports-word (+ 48 offset)))))))
  :hints (("Goal" :in-theory (e/d (data-bucket-add-publishes-three-cells)
                                 (boymoo-compiler::data-bucket-add boymoo-compiler::bucket-set
                                  boymoo-compiler::bucket-get boymoo-compiler::low-bits
                                  data-bucket-for-name)))))

(local
 (in-theory (disable boymoo-compiler::data-text boymoo-compiler::data-intern
                     boymoo-compiler::data-vector)))

(defthmd data-package-row-layout
  (mv-let (name-word with-name) (boymoo-compiler::data-text 1 name (boymoo-compiler::data-block state-data))
    (mv-let (witness witness-name with-witness)
      (boymoo-compiler::data-intern
       (boymoo-compiler::index-get name package-index) "ACL2-PKG-WITNESS"
       (boymoo-compiler::data-with-block with-name state-data))
      (declare (ignore witness-name))
      (let* ((declaration (boymoo-compiler::index-get name declarations))
             (imports (cadr declaration))
             (public-witness (if (caddr declaration) witness *proof-nil*))
             (block (boymoo-compiler::data-block with-witness))
             (start (car block)))
        (implies (integerp start)
                 (mv-let (table-word next)
                   (boymoo-compiler::data-package-vectors
                    (list name) package-index declarations state-data nil)
                   (and (equal table-word (+ 34 start))
                        (equal (boymoo-compiler::data-block next)
                               (cons (+ 48 start)
                                     (list* (+ 2 start) 2054 public-witness imports name-word 6150
                                            (cdr block))))))))))
  :hints (("Goal" :in-theory (enable data-vector-allocates-header-and-fields))))

; A row record holds its name and the address-relative word of its vector.
(defun data-package-row-records (names package-index declarations state-data)
  (if (atom names)
      (mv nil state-data)
    (let* ((name (car names))
           (number (boymoo-compiler::index-get name package-index))
           (declaration (boymoo-compiler::index-get name declarations)))
      (mv-let (name-word block)
        (boymoo-compiler::data-text 1 name (boymoo-compiler::data-block state-data))
        (mv-let (witness witness-name state-data)
          (boymoo-compiler::data-intern number "ACL2-PKG-WITNESS"
                                       (boymoo-compiler::data-with-block block state-data))
          (declare (ignore witness-name))
          (let ((fields (list name-word (cadr declaration) (if (caddr declaration) witness *proof-nil*))))
            (mv-let (row block)
              (boymoo-compiler::data-vector fields (boymoo-compiler::data-block state-data))
              (mv-let (rows state-data)
                (data-package-row-records (cdr names) package-index declarations
                                          (boymoo-compiler::data-with-block block state-data))
                (mv (cons (cons name row) rows) state-data)))))))))

(defthm data-package-row-records-follow-names
  (implies (true-listp names)
           (equal (strip-cars (car (data-package-row-records names package-index declarations state-data)))
                  names))
  :hints (("Goal" :induct (data-package-row-records names package-index declarations state-data))))

(defthmd data-package-vector-contains-ordered-rows
  (mv-let (rows state) (data-package-row-records names package-index declarations state-data)
    (mv-let (word block)
      (boymoo-compiler::data-vector (boymoo-compiler::reverse-onto prefix (strip-cdrs rows))
                                   (boymoo-compiler::data-block state))
      (equal (mv-list 2 (boymoo-compiler::data-package-vectors
                        names package-index declarations state-data prefix))
             (list word (boymoo-compiler::data-with-block block state)))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-vectors
                            names package-index declarations state-data prefix))))
