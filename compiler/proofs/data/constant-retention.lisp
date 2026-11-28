(in-package "BOYMOO-PROOFS")

(include-book "package-layout")
(include-book "tables")

(logic)
(set-verify-guards-eagerness 0)

; A cache extension keeps any previously available entry at the given
; text and leaves the resulting index well formed.
(defmacro data-constant-index-retains-p (text before after)
  `(and (data-table-p (cadr ,after) 12)
        (implies (and (stringp ,text) (boymoo-compiler::index-get ,text (cadr ,before)))
                 (equal (boymoo-compiler::index-get ,text (cadr ,after))
                        (boymoo-compiler::index-get ,text (cadr ,before))))))

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::table-get boymoo-compiler::table-put data-table-p
                     boymoo-compiler::data-text boymoo-compiler::data-fields
                     boymoo-compiler::data-list-cells boymoo-compiler::data-vector
                     boymoo-compiler::data-number boymoo-compiler::read-lines
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-part
                     boymoo-compiler::decode-symbol-part boymoo-compiler::hex-byte char length)))

(local
 (defthm bucket-insertion-keeps-the-index
   (equal (cadr (boymoo-compiler::data-bucket-add number name name-ref symbol-ref state-data))
          (cadr state-data))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-cell)))))

(local
 (defthm interning-keeps-the-index
   (equal (cadr (mv-nth 2 (boymoo-compiler::data-intern package name state-data)))
          (cadr state-data))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-bucket-add)))))

(local (in-theory (disable boymoo-compiler::data-bucket-add boymoo-compiler::data-intern)))

(defthm data-symbol-retains-constant-entry
  (implies (data-table-p (cadr state-data) 12)
           (data-constant-index-retains-p query state-data
                                         (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-symbol)))

(defthm data-atom-retains-constant-entry
  (implies (and (data-table-p (cadr state-data) 12) (stringp text))
           (data-constant-index-retains-p query state-data
                                         (mv-nth 1 (boymoo-compiler::data-atom text packages state-data)))))

(defun data-datum-token-keys-p (kind parsed)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :datum) 1 0))))
  (cond ((eq kind :datum)
         (if (consp parsed) (data-datum-token-keys-p :items parsed) (stringp parsed)))
        ((atom parsed) t)
        ((equal (car parsed) ".") t)
        (t (and (data-datum-token-keys-p :datum (car parsed))
                (data-datum-token-keys-p :items (cdr parsed))))))

(local (in-theory (disable boymoo-compiler::data-atom)))

(local
 (defthm datum-pass-retains-constant-entry
   (implies (and (data-table-p (cadr state-data) 12)
                 (data-datum-token-keys-p kind parsed))
            (data-constant-index-retains-p
             query state-data
             (mv-nth 1 (if (eq kind :datum) (boymoo-compiler::data-datum parsed packages state-data)
                         (boymoo-compiler::data-list-datum parsed packages state-data reversed)))))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-state-induction kind parsed packages state-data reversed)))))

(defthm data-datum-retains-constant-entry
  (implies (and (data-table-p (cadr state-data) 12)
                (data-datum-token-keys-p :datum parsed))
           (data-constant-index-retains-p query state-data
                                         (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data))))
  :hints (("Goal" :use ((:instance datum-pass-retains-constant-entry (kind :datum) (reversed nil)))
                  :in-theory (disable boymoo-compiler::data-datum data-datum-token-keys-p))))

(local (in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum
                           data-datum-token-keys-p)))

(defun data-constant-token-key-p (text)
  (and (stringp text)
       (or (not (equal (char text 0) #\())
           (data-datum-token-keys-p
            :datum (car (boymoo-compiler::read-lines text 0 (length text) nil nil nil (length text)))))))

(defthm data-constant-retains-existing-entry
  (implies (and (data-table-p (cadr state-data) 12)
                (data-constant-token-key-p text))
           (data-constant-index-retains-p query state-data
                                         (boymoo-compiler::data-constant text packages state-data))))

(defthm data-note-symbol-retains-constant-entry
  (implies (data-table-p (cadr state-data) 12)
           (data-constant-index-retains-p query state-data
                                         (boymoo-compiler::data-note-symbol text packages state-data))))

(local
 (defthm constant-token-key-is-text
   (implies (data-constant-token-key-p text) (stringp text))
   :rule-classes :forward-chaining))

(local
 (in-theory (disable boymoo-compiler::data-constant boymoo-compiler::data-note-symbol
                     data-constant-token-key-p)))

(defthm data-formals-retain-constant-entry
  (implies (data-table-p (cadr state-data) 12)
           (data-constant-index-retains-p query state-data
                                         (boymoo-compiler::data-formals formals packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-formals formals packages state-data))))

(local (in-theory (disable boymoo-compiler::data-formals boymoo-compiler::declaration-list)))

(defun data-term-constant-keys-p (kind parsed depth)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (and (<= depth 10000)
           (cond ((atom parsed) t)
                 ((equal (car parsed) boymoo-compiler::*quote-name*)
                  (and (data-constant-token-key-p (cadr parsed)) (null (cddr parsed))))
                 ((consp (car parsed))
                  (and (data-term-constant-keys-p :term (caddar parsed) (1+ depth))
                       (data-term-constant-keys-p :terms (cdr parsed) (1+ depth))))
                 (t (data-term-constant-keys-p :terms (cdr parsed) (1+ depth)))))
    (or (atom parsed)
        (and (data-term-constant-keys-p :term (car parsed) depth)
             (data-term-constant-keys-p :terms (cdr parsed) depth)))))

(local
 (defthm term-pass-retains-constant-entry
   (implies (and (data-table-p (cadr state-data) 12)
                 (data-term-constant-keys-p kind parsed depth))
            (data-constant-index-retains-p
             query state-data
             (if (eq kind :term) (boymoo-compiler::data-term parsed packages state-data depth)
               (boymoo-compiler::data-terms parsed packages state-data depth))))
   :rule-classes nil
   :hints (("Goal" :induct (data-term-state-induction kind parsed packages state-data depth)))))

(defthm data-term-retains-constant-entry
  (implies (and (data-table-p (cadr state-data) 12)
                (data-term-constant-keys-p :term parsed depth))
           (data-constant-index-retains-p query state-data
                                         (boymoo-compiler::data-term parsed packages state-data depth)))
  :hints (("Goal" :use ((:instance term-pass-retains-constant-entry (kind :term)))
                  :in-theory (disable boymoo-compiler::data-term data-term-constant-keys-p))))

(defthm data-term-list-retains-constant-entry
  (implies (and (data-table-p (cadr state-data) 12)
                (data-term-constant-keys-p :terms parsed depth))
           (data-constant-index-retains-p query state-data
                                         (boymoo-compiler::data-terms parsed packages state-data depth)))
  :hints (("Goal" :use ((:instance term-pass-retains-constant-entry (kind :terms)))
                  :in-theory (disable boymoo-compiler::data-terms data-term-constant-keys-p))))

(local (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms
                           data-term-constant-keys-p)))

(defun data-definition-constant-keys-p (definitions)
  (if (atom definitions)
      t
    (and (data-term-constant-keys-p :term (caddar definitions) 0)
         (data-definition-constant-keys-p (cdr definitions)))))

(defthm data-definitions-retain-constant-entry
  (implies (and (data-table-p (cadr state-data) 12)
                (data-definition-constant-keys-p definitions))
           (data-constant-index-retains-p
            query state-data (boymoo-compiler::data-definitions definitions packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-definitions definitions packages state-data))))

(defun data-program-constant-keys-p (lines)
  (if (atom lines)
      t
    (and (or (not (equal (caar lines) "define"))
             (and (data-datum-token-keys-p :datum (cadar lines))
                  (data-definition-constant-keys-p (cddar lines))))
         (data-program-constant-keys-p (cdr lines)))))

(defthm data-program-symbols-retain-constant-entry
  (implies (and (data-table-p (cadr state-data) 12) (data-program-constant-keys-p lines))
           (data-constant-index-retains-p
            query state-data (boymoo-compiler::data-program-symbols lines packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-program-symbols lines packages state-data)
                  :in-theory (disable boymoo-compiler::data-definitions data-definition-constant-keys-p))))

(defthm data-imports-retain-constant-entry
  (implies (data-table-p (cadr state-data) 12)
           (data-constant-index-retains-p
            query state-data
            (mv-nth 1 (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed))))
  :hints (("Goal" :induct (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed))))

(local (in-theory (disable boymoo-compiler::data-imports)))

(defthm data-package-vectors-keep-constant-index
  (equal (cadr (mv-nth 1 (boymoo-compiler::data-package-vectors names packages declarations state-data reversed)))
         (cadr state-data))
  :hints (("Goal" :induct (boymoo-compiler::data-package-vectors names packages declarations state-data reversed))))

(defthm data-package-declarations-retain-constant-entry
  (implies (data-table-p (cadr state-data) 12)
           (data-constant-index-retains-p
            query state-data
            (mv-nth 1 (boymoo-compiler::data-package-declarations
                       lines packages declared declarations state-data names))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-declarations
                           lines packages declared declarations state-data names))))

(defthm data-packages-retain-constant-entry
  (implies (data-table-p (cadr state-data) 12)
           (data-constant-index-retains-p query state-data
                                         (mv-nth 1 (boymoo-compiler::data-packages
                                                    lines number packages state-data reversed))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-package-declarations
                                      boymoo-compiler::data-package-vectors))))

(local
 (defthm initial-constant-index-is-well-formed
   (data-table-p (cadr (mv-nth 2 (boymoo-compiler::data-initial package))) 12)))

(defthmd data-build-retains-nil-and-t-index-entries
  (implies (and (data-program-constant-keys-p lines)
                (boymoo-compiler::index-get
                 "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
           (let ((index (mv-nth 1 (boymoo-compiler::data-build lines package-lines))))
             (and (data-table-p index 12)
                  (equal (boymoo-compiler::index-get boymoo-compiler::*nil-name* index) *proof-nil*)
                  (equal (boymoo-compiler::index-get "COMMON-LISP::T" index) *proof-t*))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-program-symbols boymoo-compiler::data-packages
                                      boymoo-compiler::data-initial boymoo-compiler::data-package-numbers
                                      boymoo-compiler::data-bucket-vector boymoo-compiler::data-write))))
