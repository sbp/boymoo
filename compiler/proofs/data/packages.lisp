(in-package "BOYMOO-PROOFS")

(include-book "tables")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::decode-part data-table-p length)))

(defun data-text-bindings-p (bindings)
  (if (atom bindings)
      (null bindings)
    (and (stringp (caar bindings)) (data-text-bindings-p (cdr bindings)))))

(defun data-binding-index (bindings)
  (if (atom bindings)
      nil
    (boymoo-compiler::index-set (caar bindings) (cdar bindings)
                               (data-binding-index (cdr bindings)))))

(defthm data-binding-index-is-a-table
  (implies (data-text-bindings-p bindings)
           (data-table-p (data-binding-index bindings) 12)))

(defthm data-binding-index-lookup
  (implies (and (data-text-bindings-p bindings) (stringp query))
           (equal (boymoo-compiler::index-get query (data-binding-index bindings))
                  (cdr (assoc-equal query bindings)))))

(defun data-package-line-name (line)
  (let ((text (cadr line)))
    (boymoo-compiler::decode-part text 0 (length text))))

(defun data-package-line-names (lines)
  (if (atom lines)
      nil
    (cons (data-package-line-name (car lines)) (data-package-line-names (cdr lines)))))

(defun data-package-names-p (names)
  (if (atom names)
      (null names)
    (and (stringp (car names)) (not (equal (car names) ""))
         (data-package-names-p (cdr names)))))

(defun data-package-number-bindings-p (bindings)
  (if (atom bindings)
      (null bindings)
    (and (stringp (caar bindings)) (natp (cdar bindings))
         (data-package-number-bindings-p (cdr bindings)))))

(defthm data-package-number-bindings-are-text-bindings
  (implies (data-package-number-bindings-p bindings) (data-text-bindings-p bindings)))

(local
 (defthm number-binding-has-natural-value
   (implies (and (data-package-number-bindings-p bindings) (assoc-equal query bindings))
            (natp (cdr (assoc-equal query bindings))))))

(local
 (defthm number-binding-is-present
   (implies (data-package-number-bindings-p bindings)
            (iff (cdr (assoc-equal query bindings)) (assoc-equal query bindings)))
   :hints (("Goal" :use number-binding-has-natural-value
                   :in-theory (disable number-binding-has-natural-value)))))

(defun data-number-package-names (names next bindings)
  (if (atom names)
      bindings
    (if (assoc-equal (car names) bindings)
        (data-number-package-names (cdr names) next bindings)
      (data-number-package-names (cdr names) (1+ next)
                                 (acons (car names) next bindings)))))

(defthm data-number-package-names-are-number-bindings
  (implies (and (data-package-number-bindings-p bindings) (natp next)
                (data-package-names-p names))
           (data-package-number-bindings-p (data-number-package-names names next bindings)))
  :hints (("Goal" :induct (data-number-package-names names next bindings))))

(local
 (defun number-package-lines-induction (lines next bindings)
   (if (atom lines)
       bindings
     (if (assoc-equal (data-package-line-name (car lines)) bindings)
         (number-package-lines-induction (cdr lines) next bindings)
       (number-package-lines-induction (cdr lines) (1+ next)
                                       (acons (data-package-line-name (car lines)) next bindings))))))

(defthmd data-package-numbers-as-bindings
  (implies (and (data-package-names-p (data-package-line-names lines)) (natp next)
                (data-package-number-bindings-p bindings))
           (equal (boymoo-compiler::data-package-numbers lines next (data-binding-index bindings))
                  (data-binding-index
                   (data-number-package-names (data-package-line-names lines) next bindings))))
  :hints (("Goal" :induct (number-package-lines-induction lines next bindings))))

(defun data-first-package-names (names seen)
  (if (atom names)
      nil
    (if (member-equal (car names) seen)
        (data-first-package-names (cdr names) seen)
      (cons (car names) (data-first-package-names (cdr names) (cons (car names) seen))))))

(defun data-number-rows (names next)
  (if (atom names)
      nil
    (cons (cons (car names) next) (data-number-rows (cdr names) (1+ next)))))

(local
 (defthm package-binding-key-membership
   (implies (stringp query)
            (iff (assoc-equal query bindings) (member-equal query (strip-cars bindings))))))

(local
 (defthm package-reverse-onto-cons
   (equal (boymoo-compiler::reverse-onto (cons first rest) tail)
          (boymoo-compiler::reverse-onto rest (cons first tail)))))

(defthm data-package-bindings-in-first-declaration-order
  (implies (data-package-names-p names)
           (equal (data-number-package-names names next bindings)
                  (boymoo-compiler::reverse-onto
                   (data-number-rows (data-first-package-names names (strip-cars bindings)) next)
                   bindings)))
  :hints (("Goal" :induct (data-number-package-names names next bindings))))

(defthmd data-package-numbers-first-order
  (implies (data-package-names-p (data-package-line-names package-lines))
           (equal (boymoo-compiler::data-package-numbers package-lines 0 nil)
                  (data-binding-index
                   (boymoo-compiler::reverse-onto
                    (data-number-rows (data-first-package-names
                                       (data-package-line-names package-lines) nil) 0)
                    nil))))
  :hints (("Goal" :use ((:instance data-package-numbers-as-bindings
                                   (lines package-lines) (next 0) (bindings nil)))
                  :in-theory (disable boymoo-compiler::data-package-numbers data-binding-index))))

(defun data-package-import-lines-agree-p (lines name imports)
  (if (atom lines)
      t
    (and (implies (equal name (data-package-line-name (car lines)))
                  (equal imports (caddar lines)))
         (data-package-import-lines-agree-p (cdr lines) name imports))))

(defun data-package-lines-consistent-p (lines)
  (if (atom lines)
      (null lines)
    (let ((name (data-package-line-name (car lines))))
      (and (stringp name)
           (data-package-import-lines-agree-p (cdr lines) name (caddar lines))
           (data-package-lines-consistent-p (cdr lines))))))

(defun data-package-declarations-compatible-p (lines declarations)
  (if (atom lines)
      t
    (let ((old (boymoo-compiler::index-get (data-package-line-name (car lines)) declarations)))
      (and (or (not old) (equal (car old) (caddar lines)))
           (data-package-declarations-compatible-p (cdr lines) declarations)))))

(defun data-package-declarations-membership-p (lines declarations names)
  (if (atom lines)
      t
    (let ((name (data-package-line-name (car lines))))
      (and (iff (boymoo-compiler::index-get name declarations) (member-equal name names))
           (data-package-declarations-membership-p (cdr lines) declarations names)))))

(defun data-package-visible-in-lines-p (name lines)
  (if (atom lines)
      nil
    (or (and (equal name (data-package-line-name (car lines))) (equal (caar lines) "package"))
        (data-package-visible-in-lines-p name (cdr lines)))))

(defun data-package-first-import-text (name lines)
  (if (atom lines)
      nil
    (if (equal name (data-package-line-name (car lines))) (caddar lines)
      (data-package-first-import-text name (cdr lines)))))

(local
 (defthm compatibility-of-new-declaration
   (implies (and (data-table-p declarations 12) (stringp name)
                 (data-package-lines-consistent-p lines)
                 (data-package-declarations-compatible-p lines declarations)
                 (data-package-import-lines-agree-p lines name imports))
            (data-package-declarations-compatible-p
             lines (boymoo-compiler::index-set name (list imports ref visible) declarations)))))

(local
 (defthm membership-of-unseen-declaration
   (implies (and (data-table-p declarations 12) (stringp name)
                 (data-package-lines-consistent-p lines) record
                 (data-package-declarations-membership-p lines declarations names)
                 (not (member-equal name names)))
            (data-package-declarations-membership-p
             lines (boymoo-compiler::index-set name record declarations) (cons name names)))
   :hints (("Goal" :induct (data-package-declarations-membership-p lines declarations names)))))

(local
 (defthm membership-of-seen-declaration
   (implies (and (data-table-p declarations 12) (stringp name)
                 (data-package-lines-consistent-p lines) record
                 (data-package-declarations-membership-p lines declarations names)
                 (member-equal name names))
            (data-package-declarations-membership-p
             lines (boymoo-compiler::index-set name record declarations) names))
   :hints (("Goal" :induct (data-package-declarations-membership-p lines declarations names)))))

(local
 (in-theory (disable boymoo-compiler::data-imports boymoo-compiler::reverse-onto)))

(defthmd data-package-declarations-first-order
  (implies (and (data-table-p declarations 12)
                (data-package-lines-consistent-p lines)
                (data-package-declarations-compatible-p lines declarations)
                (data-package-declarations-membership-p lines declarations names))
           (equal (mv-nth 2 (boymoo-compiler::data-package-declarations
                             lines package-index declared declarations state-data names))
                  (boymoo-compiler::reverse-onto
                   names (data-first-package-names (data-package-line-names lines) names))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-declarations
                            lines package-index declared declarations state-data names))))

(defthmd data-package-declarations-visibility
  (implies (and (stringp query) (data-table-p declarations 12)
                (data-package-lines-consistent-p lines)
                (data-package-declarations-compatible-p lines declarations))
           (iff (caddr (boymoo-compiler::index-get
                        query (car (boymoo-compiler::data-package-declarations
                                    lines package-index declared declarations state-data names))))
                (or (caddr (boymoo-compiler::index-get query declarations))
                    (data-package-visible-in-lines-p query lines))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-declarations
                            lines package-index declared declarations state-data names))))

(defthmd data-package-declarations-import-text
  (implies (and (stringp query) (data-table-p declarations 12)
                (data-package-lines-consistent-p lines)
                (data-package-declarations-compatible-p lines declarations))
           (equal (car (boymoo-compiler::index-get
                        query (car (boymoo-compiler::data-package-declarations
                                    lines package-index declared declarations state-data names))))
                  (let ((old (boymoo-compiler::index-get query declarations)))
                    (if old (car old) (data-package-first-import-text query lines)))))
  :hints (("Goal" :induct (boymoo-compiler::data-package-declarations
                            lines package-index declared declarations state-data names))))
