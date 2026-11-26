(in-package "BOYMOO-PROOFS")

(include-book "term-spelling")

(logic)
(set-verify-guards-eagerness 0)

; The status of symbol lookup is separate from its value because NIL
; is a symbol. The witness belongs to the symbol's home package.
(defun data-elaborate-symbol (text packages)
  (let* ((split (boymoo-compiler::symbol-separator text))
         (package-name (boymoo-compiler::decode-symbol-part text 0 split))
         (name (boymoo-compiler::decode-symbol-part text (+ 2 split) (length text)))
         (package (assoc-equal package-name packages))
         (witness (proof-package-witness package))
         (symbol (intern-in-package-of-symbol name witness)))
    (mv (and (stringp text) split package (symbolp witness) (symbolp symbol)
             (data-symbol-spelling-p text split package-name name)
             (equal (symbol-name symbol) name) (equal (symbol-package-name symbol) package-name))
        symbol)))

(local
 (in-theory (disable boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                     data-symbol-spelling-p intern-in-package-of-symbol length)))

(defthmd data-elaborated-symbol-agrees-with-text
  (mv-let (ok symbol) (data-elaborate-symbol text packages)
    (implies ok (data-source-symbol-agrees-p text symbol))))

(local (in-theory (disable data-elaborate-symbol data-source-symbol-agrees-p)))

(defun data-elaborate-symbols (texts packages)
  (if (atom texts)
      (mv (null texts) nil)
    (mv-let (first-ok first) (data-elaborate-symbol (car texts) packages)
      (mv-let (rest-ok rest) (data-elaborate-symbols (cdr texts) packages)
        (mv (and first-ok rest-ok) (cons first rest))))))

(defthmd data-elaborated-symbols-agree-with-text
  (mv-let (ok symbols) (data-elaborate-symbols texts packages)
    (implies ok (data-source-symbols-agree-p texts symbols)))
  :hints (("Goal" :induct (data-elaborate-symbols texts packages)
                  :in-theory (e/d (data-elaborated-symbol-agrees-with-text) (mv-nth)))))

(local (in-theory (disable data-elaborate-symbols boymoo-compiler::declaration-list)))

(defun data-elaborate-term (kind parsed packages bindings)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (cond ((atom parsed) (data-elaborate-symbol parsed packages))
            ((equal (car parsed) boymoo-compiler::*quote-name*)
             (let ((binding (assoc-equal (cadr parsed) bindings)))
               (mv (and (stringp (cadr parsed)) (null (cddr parsed)) (consp binding))
                   (list 'quote (cdr binding)))))
            ((consp (car parsed))
             (let ((head (car parsed)))
               (mv-let (formals-ok formals)
                 (data-elaborate-symbols (boymoo-compiler::declaration-list (cadr head)) packages)
                 (mv-let (body-ok body) (data-elaborate-term :term (caddr head) packages bindings)
                   (mv-let (args-ok args) (data-elaborate-term :terms (cdr parsed) packages bindings)
                     (mv (and (equal (car head) "COMMON-LISP::LAMBDA") (consp (cddr head)) (null (cdddr head))
                              formals-ok body-ok args-ok)
                         (cons (list 'lambda formals body) args)))))))
            (t
             (mv-let (head-ok head) (data-elaborate-symbol (car parsed) packages)
               (mv-let (args-ok args) (data-elaborate-term :terms (cdr parsed) packages bindings)
                 (mv (and head-ok args-ok) (cons head args))))))
    (if (atom parsed)
        (mv (null parsed) nil)
      (mv-let (first-ok first) (data-elaborate-term :term (car parsed) packages bindings)
        (mv-let (rest-ok rest) (data-elaborate-term :terms (cdr parsed) packages bindings)
          (mv (and first-ok rest-ok) (cons first rest)))))))

(defthmd data-elaborated-term-agrees-with-text
  (mv-let (ok source) (data-elaborate-term kind parsed packages bindings)
    (implies ok (if (eq kind :term) (data-source-term-agrees-p parsed source bindings)
                  (data-source-terms-agree-p parsed source bindings))))
  :hints (("Goal" :induct (data-elaborate-term kind parsed packages bindings)
                  :in-theory (e/d (data-elaborated-symbol-agrees-with-text
                                   data-elaborated-symbols-agree-with-text)
                                  (mv-nth assoc-equal data-source-symbols-agree-p)))))

(defthmd data-elaborated-term-fits-builder-inputs
  (mv-let (ok source) (data-elaborate-term :term parsed packages bindings)
    (implies (and ok (data-term-depth-bounded-p :term parsed depth)
                  (data-quote-spellings-p bindings witnesses))
             (and (data-source-term-agrees-p parsed source bindings)
                  (data-term-storage-input-p :term parsed depth)
                  (data-term-constant-keys-p :term parsed depth))))
  :hints (("Goal" :use ((:instance data-elaborated-term-agrees-with-text (kind :term))
                        (:instance data-related-term-fits-storage
                                   (source (mv-nth 1 (data-elaborate-term :term parsed packages bindings)))))
                  :in-theory (disable data-elaborate-term data-source-term-agrees-p
                                      data-term-depth-bounded-p data-quote-spellings-p
                                      data-term-storage-input-p data-term-constant-keys-p mv-nth))))
