(in-package "BOYMOO-PROOFS")

(include-book "sizing")

(logic)
(set-verify-guards-eagerness 0)

(defun data-state-buckets-p (state-data)
  (data-static-bucket-tree-p (caddr state-data) 12))

(defthm data-empty-state-has-bucket-tree
  (data-state-buckets-p nil))

(local
 (in-theory (disable data-state-buckets-p data-static-bucket-tree-p
                     boymoo-compiler::bucket-get boymoo-compiler::bucket-set
                     boymoo-compiler::low-bits boymoo-compiler::text-hash ash)))

(local
 (defthm state-with-empty-bucket-slot
   (implies (null (caddr state-data)) (data-state-buckets-p state-data))
   :hints (("Goal" :in-theory (enable data-state-buckets-p)))))

(local
 (defthm data-with-block-frames-buckets
   (implies (data-state-buckets-p state-data)
            (data-state-buckets-p (boymoo-compiler::data-with-block block state-data)))
   :hints (("Goal" :in-theory (enable data-state-buckets-p)))))

(local
 (defthm data-remember-frames-buckets
   (implies (data-state-buckets-p state-data)
            (data-state-buckets-p (boymoo-compiler::data-remember text word state-data)))
   :hints (("Goal" :in-theory (enable data-state-buckets-p)))))

(local
 (defthm data-replacing-name-table-frames-buckets
   (implies (data-state-buckets-p state-data)
            (data-state-buckets-p (cons names (cdr state-data))))
   :hints (("Goal" :in-theory (enable data-state-buckets-p)))))

(defthm data-bucket-add-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p
            (boymoo-compiler::data-bucket-add package name name-ref symbol-ref state-data)))
  :hints (("Goal" :in-theory (enable data-state-buckets-p))))

(local
 (in-theory (disable boymoo-compiler::data-with-block boymoo-compiler::data-remember
                     boymoo-compiler::data-bucket-add boymoo-compiler::index-get
                     boymoo-compiler::index-set boymoo-compiler::table-get
                     boymoo-compiler::table-put boymoo-compiler::data-text
                     boymoo-compiler::data-number boymoo-compiler::data-fields
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part)))

(local
 (defthm name-table-extension-frames-buckets
   (implies (data-state-buckets-p state-data)
            (data-state-buckets-p (list* names constants (caddr state-data) block)))
   :hints (("Goal" :in-theory (enable data-state-buckets-p)))))

(defthm data-intern-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 2 (boymoo-compiler::data-intern package name state-data)))))

(local (in-theory (disable boymoo-compiler::data-intern)))

(defthm data-symbol-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-symbol)))

(defthm data-atom-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-atom text packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-atom boymoo-compiler::data-list-cells)))

(defun data-datum-state-induction (kind parsed packages state-data reversed)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :datum) 1 0))))
  (cond ((eq kind :datum)
         (if (consp parsed)
             (data-datum-state-induction :items parsed packages state-data nil)
           (list packages state-data reversed)))
        ((or (atom parsed) (equal (car parsed) ".")) (list packages state-data reversed))
        (t (mv-let (word next) (boymoo-compiler::data-datum (car parsed) packages state-data)
             (list (data-datum-state-induction :datum (car parsed) packages state-data nil)
                   (data-datum-state-induction :items (cdr parsed) packages next (cons word reversed)))))))

(local
 (defthm datum-pass-preserves-buckets
   (implies (data-state-buckets-p state-data)
            (if (eq kind :datum)
                (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data)))
              (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-list-datum
                                              parsed packages state-data reversed)))))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-state-induction kind parsed packages state-data reversed)))))

(defthm data-datum-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data))))
  :hints (("Goal" :use ((:instance datum-pass-preserves-buckets (kind :datum) (reversed nil)))
                  :in-theory (disable boymoo-compiler::data-datum))))

(local
 (in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum
                     boymoo-compiler::read-lines)))

(defthm data-constant-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (boymoo-compiler::data-constant text packages state-data))))

(defthm data-note-symbol-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (boymoo-compiler::data-note-symbol text packages state-data))))

(local
 (in-theory (disable boymoo-compiler::data-constant boymoo-compiler::data-note-symbol)))

(defthm data-formals-preserve-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (boymoo-compiler::data-formals formals packages state-data))))

(local (in-theory (disable boymoo-compiler::data-formals)))

(defun data-term-state-induction (kind parsed packages state-data depth)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (cond ((or (< 10000 depth) (atom parsed) (equal (car parsed) boymoo-compiler::*quote-name*))
             (list packages state-data depth))
            ((consp (car parsed))
             (let* ((head (car parsed))
                    (named (boymoo-compiler::data-note-symbol (car head) packages state-data))
                    (bound (boymoo-compiler::data-formals
                            (boymoo-compiler::declaration-list (cadr head)) packages named))
                    (body (boymoo-compiler::data-term (caddr head) packages bound (1+ depth))))
               (list (data-term-state-induction :term (caddr head) packages bound (1+ depth))
                     (data-term-state-induction :terms (cdr parsed) packages body (1+ depth)))))
            (t (data-term-state-induction :terms (cdr parsed) packages
                                          (boymoo-compiler::data-note-symbol (car parsed) packages state-data)
                                          (1+ depth))))
    (if (atom parsed)
        (list packages state-data depth)
      (let ((next (boymoo-compiler::data-term (car parsed) packages state-data depth)))
        (list (data-term-state-induction :term (car parsed) packages state-data depth)
              (data-term-state-induction :terms (cdr parsed) packages next depth))))))

(local
 (defthm term-pass-preserves-buckets
   (implies (data-state-buckets-p state-data)
            (if (eq kind :term)
                (data-state-buckets-p (boymoo-compiler::data-term parsed packages state-data depth))
              (data-state-buckets-p (boymoo-compiler::data-terms parsed packages state-data depth))))
   :rule-classes nil
   :hints (("Goal" :induct (data-term-state-induction kind parsed packages state-data depth)))))

(defthm data-term-preserves-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (boymoo-compiler::data-term parsed packages state-data depth)))
  :hints (("Goal" :use ((:instance term-pass-preserves-buckets (kind :term)))
                  :in-theory (disable boymoo-compiler::data-term))))

(local (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms)))

(defthm data-definitions-preserve-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (boymoo-compiler::data-definitions items packages state-data))))

(defthm data-program-symbols-preserve-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (boymoo-compiler::data-program-symbols lines packages state-data)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-definitions))))

(defthm data-imports-preserve-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-imports
                                           imports number packages common-lisp state-data reversed)))))

(local (in-theory (disable boymoo-compiler::data-imports boymoo-compiler::data-vector)))

(defthm data-package-vectors-preserve-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-package-vectors
                                           names packages declarations state-data reversed)))))

(defthm data-package-declarations-preserve-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-package-declarations
                                           lines packages declared declarations state-data names)))))

(defthm data-packages-preserve-bucket-tree
  (implies (data-state-buckets-p state-data)
           (data-state-buckets-p (mv-nth 1 (boymoo-compiler::data-packages
                                           lines number packages state-data reversed))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-package-vectors
                                      boymoo-compiler::data-package-declarations))))

(defthm data-initial-has-bucket-tree
  (data-state-buckets-p (mv-nth 2 (boymoo-compiler::data-initial package))))

(defthm data-initial-constant-index-has-nil-and-t
  (let ((index (cadr (mv-nth 2 (boymoo-compiler::data-initial package)))))
    (and (equal (boymoo-compiler::index-get "COMMON-LISP::NIL" index) *proof-nil*)
         (equal (boymoo-compiler::index-get "COMMON-LISP::T" index) *proof-t*))))

(defthm data-build-body-has-bucket-tree
  (data-state-buckets-p (mv-nth 2 (data-before-buckets lines package-lines)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-packages
                                      boymoo-compiler::data-initial
                                      boymoo-compiler::data-program-symbols))))

(defthmd data-build-count-matches-image-for-sized-body
  (mv-let (common-lisp package-word state-data) (data-before-buckets lines package-lines)
    (declare (ignore package-word))
    (implies (and common-lisp (data-block-sized-p (boymoo-compiler::data-block state-data) 80))
             (proof-image-p (car (boymoo-compiler::data-build lines package-lines)))))
  :hints (("Goal" :use (data-build-count-matches-image-under-body-invariant
                       data-build-body-has-bucket-tree)
                  :in-theory (e/d (data-state-buckets-p)
                                 (data-build-body-has-bucket-tree data-before-buckets
                                  boymoo-compiler::data-build proof-image-p data-block-sized-p)))))
