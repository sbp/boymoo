(in-package "BOYMOO-PROOFS")

(include-book "rows")
(include-book "collections")

(logic)
(set-verify-guards-eagerness 0)

; An import is recorded when its home binding supplies the symbol and
; the importing package has an unused name. The list result omits the
; final cons-cell allocation and lists the words in declaration order.
(defun data-import-word-records (imports number packages common-lisp state-data)
  (if (atom imports)
      (mv (null imports) nil state-data)
    (let ((text (car imports)))
      (mv-let (symbol-word named) (boymoo-compiler::data-symbol text packages state-data)
        (let* ((split (boymoo-compiler::symbol-separator text))
               (name (boymoo-compiler::decode-symbol-part text (+ 2 split) (length text)))
               (home (or (boymoo-compiler::index-get (boymoo-compiler::decode-symbol-part text 0 split) packages)
                         common-lisp))
               (entry (data-name-table-lookup home name named)))
          (if (and (stringp name) (not (equal name "ACL2-PKG-WITNESS"))
                   (unsigned-byte-p 64 symbol-word) (consp entry) (equal (car entry) symbol-word)
                   (not (data-name-table-lookup number name named)))
              (let* ((hash (+ (boymoo-compiler::text-hash name) (* 7919 number)))
                     (names (boymoo-compiler::table-put (cons number name) (cons :import entry)
                                                       hash 12 (car named)))
                     (next (boymoo-compiler::data-bucket-add number name (cdr entry) symbol-word
                                                            (cons names (cdr named)))))
                (mv-let (ok words state-data)
                  (data-import-word-records (cdr imports) number packages common-lisp next)
                  (mv ok (cons symbol-word words) state-data)))
            (mv nil nil named)))))))

(local
 (in-theory (disable boymoo-compiler::data-symbol boymoo-compiler::index-get boymoo-compiler::table-get
                     boymoo-compiler::table-put boymoo-compiler::data-bucket-add boymoo-compiler::text-hash
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part length)))

(defthm data-import-word-records-have-one-word-per-import
  (mv-let (ok words next) (data-import-word-records imports number packages common-lisp state-data)
    (declare (ignore next))
    (implies ok (equal (len words) (len imports))))
  :hints (("Goal" :induct (data-import-word-records imports number packages common-lisp state-data))))

(local
 (defthm accumulate-first-import
   (equal (boymoo-compiler::reverse-onto (cons word rest) reversed)
          (boymoo-compiler::reverse-onto rest (cons word reversed)))))

(local
 (defthm accumulate-no-imports
   (equal (boymoo-compiler::reverse-onto nil reversed) reversed)))

(local
 (in-theory (disable boymoo-compiler::reverse-onto boymoo-compiler::data-list-cells
                     boymoo-compiler::data-with-block boymoo-compiler::data-block)))

(defthmd data-imports-allocate-recorded-words-in-declaration-order
  (mv-let (ok words named) (data-import-word-records imports number packages common-lisp state-data)
    (implies ok
             (mv-let (result block)
               (boymoo-compiler::data-list-cells (boymoo-compiler::reverse-onto words reversed)
                                                 *proof-nil* (boymoo-compiler::data-block named))
               (equal (mv-list 2 (boymoo-compiler::data-imports
                                  imports number packages common-lisp state-data reversed))
                      (list result (boymoo-compiler::data-with-block block named))))))
  :hints (("Goal" :induct (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed))))

(local (in-theory (disable data-import-word-records boymoo-compiler::data-imports)))

(defthmd data-view-of-package-import-list
  (mv-let (ok words named) (data-import-word-records imports number package-index common-lisp state-data)
    (let* ((block (boymoo-compiler::data-block named))
           (reversed (boymoo-compiler::reverse-onto words nil))
           (ref (car (boymoo-compiler::data-imports imports number package-index common-lisp state-data nil))))
      (implies (and ok (integerp (car block))
                    (proof-value-p *proof-nil* nil base objects packages machine)
                    (data-list-cell-view-layout-p reversed reversed-values *proof-nil* (car block)
                                                  base objects packages machine))
               (proof-value-p (proof-constant-word ref) (boymoo-compiler::reverse-onto reversed-values nil)
                              base objects packages machine))))
  :hints (("Goal" :use ((:instance data-imports-allocate-recorded-words-in-declaration-order
                                   (packages package-index) (reversed nil))
                       (:instance data-view-of-static-list-cell-block
                                  (words (boymoo-compiler::reverse-onto
                                          (mv-nth 1 (data-import-word-records
                                                     imports number package-index common-lisp state-data)) nil))
                                  (values reversed-values) (tail *proof-nil*) (tail-value nil)
                                  (block (boymoo-compiler::data-block
                                          (mv-nth 2 (data-import-word-records
                                                     imports number package-index common-lisp state-data))))))
                  :in-theory (disable data-list-cell-view-layout-p proof-value-p))))
