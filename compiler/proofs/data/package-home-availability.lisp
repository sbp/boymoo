(in-package "BOYMOO-PROOFS")

(include-book "symbol-quotes")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::table-get boymoo-compiler::table-put
                     boymoo-compiler::data-symbol boymoo-compiler::data-intern boymoo-compiler::data-bucket-add
                     boymoo-compiler::data-with-block boymoo-compiler::data-block boymoo-compiler::data-list-cells
                     boymoo-compiler::data-vector boymoo-compiler::data-text
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                     boymoo-compiler::decode-part boymoo-compiler::text-hash boymoo-compiler::declaration-list
                     data-table-p data-natural-table-values-p length char)))

(defun data-imports-leave-home-name-p (imports number home name)
  (if (atom imports)
      t
    (let* ((text (car imports))
           (split (boymoo-compiler::symbol-separator text))
           (import-name (boymoo-compiler::decode-symbol-part text (+ 2 split) (length text))))
      (and (stringp import-name)
           (not (equal (cons number import-name) (cons home name)))
           (data-imports-leave-home-name-p (cdr imports) number home name)))))

(local
 (defthm installing-an-import-at-a-different-key-keeps-available-home
   (implies (and (natp number) (natp home) (stringp import-name) (stringp name)
                 (not (equal (cons number import-name) (cons home name)))
                 (data-home-available-state-p home name state-data))
            (data-home-available-state-p
             home name
             (boymoo-compiler::data-bucket-add
              number import-name name-word symbol-word
              (cons (boymoo-compiler::table-put
                     (cons number import-name) value
                     (+ (* 7919 number) (boymoo-compiler::text-hash import-name)) 12 (car state-data))
                    (cdr state-data)))))))

(local (in-theory (disable data-home-available-state-p)))

(defthmd data-imports-preserve-available-home-outside-imported-keys
  (implies (and (natp number) (natp home) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p home name state-data)
                (data-imports-leave-home-name-p imports number home name))
           (data-home-available-state-p
            home name
            (mv-nth 1 (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed))))
  :hints (("Goal" :induct (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed))))

(defun data-known-package-names-p (names packages)
  (if (atom names)
      (null names)
    (and (natp (boymoo-compiler::index-get (car names) packages))
         (data-known-package-names-p (cdr names) packages))))

(local
 (defthm reversing-keeps-package-names-known
   (implies (and (data-known-package-names-p names packages) (data-known-package-names-p reversed packages))
            (data-known-package-names-p (boymoo-compiler::reverse-onto names reversed) packages))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto names reversed)))))

(local
 (in-theory (disable boymoo-compiler::data-imports data-imports-leave-home-name-p boymoo-compiler::reverse-onto)))

(defun data-package-lines-leave-home-name-p (lines packages home name)
  (if (atom lines)
      t
    (let* ((line (car lines))
           (package-name (data-package-line-name line))
           (number (boymoo-compiler::index-get package-name packages))
           (imports (boymoo-compiler::declaration-list (caddr line))))
      (and (natp number)
           (data-imports-leave-home-name-p imports number home name)
           (data-package-lines-leave-home-name-p (cdr lines) packages home name)))))

(defthmd data-package-declarations-preserve-home-outside-imported-keys
  (implies (and (natp home) (stringp name) (data-natural-table-values-p declared 12)
                (data-home-available-state-p home name state-data)
                (data-known-package-names-p names packages)
                (data-package-lines-leave-home-name-p lines packages home name))
           (mv-let (next-declarations after-packages next-names)
             (boymoo-compiler::data-package-declarations lines packages declared declarations state-data names)
             (declare (ignore next-declarations))
             (and (data-home-available-state-p home name after-packages)
                  (data-known-package-names-p next-names packages))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-declarations
                          lines packages declared declarations state-data names)
                  :in-theory (enable data-imports-preserve-available-home-outside-imported-keys))))

(local
 (in-theory (disable boymoo-compiler::data-package-declarations data-package-lines-leave-home-name-p)))

(defthmd data-package-vectors-preserve-available-home
  (implies (and (natp home) (stringp name) (data-home-available-state-p home name state-data)
                (data-known-package-names-p names packages))
           (data-home-available-state-p
            home name
            (mv-nth 1 (boymoo-compiler::data-package-vectors names packages declarations state-data reversed))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-vectors names packages declarations state-data reversed))))

(local
 (defthm empty-list-has-no-unknown-package-names
   (data-known-package-names-p nil packages)))

(local (in-theory (disable boymoo-compiler::data-package-vectors data-known-package-names-p)))

(defthmd data-packages-preserve-home-outside-imported-keys
  (implies (and (natp home) (stringp name) (data-home-available-state-p home name state-data)
                (data-package-lines-leave-home-name-p lines packages home name))
           (data-home-available-state-p
            home name (mv-nth 1 (boymoo-compiler::data-packages lines number packages state-data reversed))))
  :hints (("Goal" :use ((:instance data-package-declarations-preserve-home-outside-imported-keys
                                   (declared nil) (declarations nil) (names nil)))
                  :in-theory (enable data-package-vectors-preserve-available-home))))

(local
 (defthm empty-name-table-has-no-name-binding
   (equal (boymoo-compiler::table-get key hash bits nil) nil)
   :hints (("Goal" :in-theory (enable boymoo-compiler::table-get)))))

(local
 (defthm looking-up-a-name-after-setting-one
   (let ((query (cons home name))
         (key (cons package new-name))
         (query-hash (+ (boymoo-compiler::text-hash name) (* 7919 home)))
         (hash (+ (boymoo-compiler::text-hash new-name) (* 7919 package))))
     (implies (and (natp home) (stringp name) (natp package) (stringp new-name)
                   (data-table-p names 12))
              (equal (boymoo-compiler::table-get
                      query query-hash 12 (boymoo-compiler::table-put key entry hash 12 names))
                     (if (equal query key) entry
                       (boymoo-compiler::table-get query query-hash 12 names)))))
   :hints (("Goal" :use ((:instance data-table-get-after-put
                                    (query (cons home name)) (key (cons package new-name))
                                    (query-hash (+ (boymoo-compiler::text-hash name) (* 7919 home)))
                                    (hash (+ (boymoo-compiler::text-hash new-name) (* 7919 package)))
                                    (value entry) (bits 12) (tree names)))
                   :in-theory (disable data-table-get-after-put)))))

(defthmd data-fixed-symbol-initialization-keeps-available-home
  (implies (and (natp common-lisp) (natp home) (stringp name))
           (data-home-available-state-p
            home name (mv-nth 2 (boymoo-compiler::data-initial common-lisp))))
  :hints (("Goal" :in-theory (e/d (data-home-available-state-p)
                                 ((:executable-counterpart boymoo-compiler::text-hash))))))

(local
 (in-theory (disable boymoo-compiler::data-initial boymoo-compiler::data-packages
                     boymoo-compiler::data-package-numbers)))

(defthmd data-building-packages-leaves-home-outside-imported-keys
  (let* ((packages (boymoo-compiler::data-package-numbers package-lines 0 nil))
         (common-lisp (boymoo-compiler::index-get "COMMON-LISP" packages))
         (home (boymoo-compiler::index-get (symbol-package-name symbol) packages)))
    (implies (and (symbolp symbol) common-lisp home
                  (data-package-lines-leave-home-name-p package-lines packages home (symbol-name symbol)))
             (data-build-home-available-p package-lines symbol)))
  :hints (("Goal" :in-theory (enable data-fixed-symbol-initialization-keeps-available-home
                                    data-packages-preserve-home-outside-imported-keys))))

(defthmd data-build-records-a-symbol-quote-outside-imported-home-keys
  (let* ((packages (boymoo-compiler::data-package-numbers package-lines 0 nil))
         (home (boymoo-compiler::index-get (symbol-package-name symbol) packages)))
    (implies (and (symbolp symbol) (data-atom-spells-value-p query symbol)
                  (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                  (boymoo-compiler::index-get "COMMON-LISP" packages) home
                  (data-package-lines-leave-home-name-p package-lines packages home (symbol-name symbol))
                  (< 0 (data-program-quote-count lines query)))
             (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))))
  :hints (("Goal" :use (data-building-packages-leaves-home-outside-imported-keys
                        data-build-records-every-spelled-symbol-quote-with-available-home)
                  :in-theory (disable data-atom-spells-value-p data-build-home-available-p
                                      data-program-storage-input-p data-program-constant-keys-p
                                      data-program-quote-count boymoo-compiler::data-build))))

(defthmd data-checked-text-records-a-symbol-quote-outside-imported-home-keys
  (let* ((parsed (boymoo-compiler::read-program text))
         (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
         (packages (boymoo-compiler::data-package-numbers package-lines 0 nil))
         (value (cdr (assoc-equal query bindings)))
         (home (boymoo-compiler::index-get (symbol-package-name value) packages)))
    (implies (and (data-program-spans-p text events lines)
                  (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-quote-spellings-p bindings witnesses)
                  (< 0 (data-program-quote-count lines query))
                  (symbolp value) home (boymoo-compiler::index-get "COMMON-LISP" packages)
                  (data-package-lines-leave-home-name-p package-lines packages home (symbol-name value)))
             (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build parsed package-lines)))))
  :hints (("Goal" :use (data-checked-text-records-a-symbol-quote-with-available-home
                        (:instance data-building-packages-leaves-home-outside-imported-keys
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil)))
                                   (symbol (cdr (assoc-equal query bindings)))))
                  :in-theory (disable data-build-home-available-p data-program-spans-p data-source-lines-spelled-p
                                      data-quote-spellings-p data-program-quote-count boymoo-compiler::read-program
                                      boymoo-compiler::index-lines boymoo-compiler::data-build))))
