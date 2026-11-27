(in-package "BOYMOO-PROOFS")

(include-book "datum-spelling")
(include-book "quote-visits")

(logic)
(set-verify-guards-eagerness 0)

; Each quotation has the same value in the source relation and in the
; spelling witness. A witness supplies the spans of a compound datum.
(defun data-quote-spellings-p (bindings witnesses)
  (if (atom bindings)
      (and (null bindings) (null witnesses))
    (and (consp witnesses)
         (data-constant-spells-value-p (caar bindings) (caar witnesses) (cadar witnesses) (cdar bindings))
         (data-quote-spellings-p (cdr bindings) (cdr witnesses)))))

(defun data-quote-witness-for-text (text bindings witnesses)
  (cond ((atom bindings) nil)
        ((equal text (caar bindings)) (car witnesses))
        (t (data-quote-witness-for-text text (cdr bindings) (cdr witnesses)))))

(local
 (in-theory (disable data-constant-spells-value-p data-constant-storage-input-p
                     data-constant-token-key-p data-symbol-storage-input-p data-source-symbol-agrees-p)))

(defthmd data-quote-lookup-has-its-checked-spelling
  (let ((witness (data-quote-witness-for-text text bindings witnesses))
        (binding (assoc-equal text bindings)))
    (implies (and (data-quote-spellings-p bindings witnesses) binding)
             (data-constant-spells-value-p text (car witness) (cadr witness) (cdr binding))))
  :hints (("Goal" :induct (data-quote-witness-for-text text bindings witnesses))))

(local
 (defthm looked-up-quote-fits-storage
   (implies (and (data-quote-spellings-p bindings witnesses) (assoc-equal text bindings))
            (and (data-constant-storage-input-p text) (data-constant-token-key-p text)))
   :rule-classes ((:forward-chaining :trigger-terms ((data-quote-spellings-p bindings witnesses)
                                                    (assoc-equal text bindings))))
   :hints (("Goal" :induct (data-quote-spellings-p bindings witnesses))
           ("Subgoal *1/3" :use ((:instance data-constant-spelling-fits-storage
                                            (text (caar bindings)) (events (caar witnesses))
                                            (parsed (cadar witnesses)) (value (cdar bindings))))))))

(local
 (defthm source-symbol-spellings-fit-storage
   (implies (data-source-symbol-agrees-p text name) (data-symbol-storage-input-p text))
   :rule-classes :forward-chaining
   :hints (("Goal" :use ((:instance data-related-source-symbol-fits-storage (symbol name)))))))

(defthm data-related-formals-fit-storage
  (implies (data-source-symbols-agree-p formals symbols)
           (data-formals-storage-input-p formals))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (data-source-symbols-agree-p formals symbols))))

(defun data-term-depth-bounded-p (kind parsed depth)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (and (<= depth 10000)
           (cond ((or (atom parsed) (equal (car parsed) boymoo-compiler::*quote-name*)) t)
                 ((consp (car parsed))
                  (and (data-term-depth-bounded-p :term (caddar parsed) (1+ depth))
                       (data-term-depth-bounded-p :terms (cdr parsed) (1+ depth))))
                 (t (data-term-depth-bounded-p :terms (cdr parsed) (1+ depth)))))
    (or (atom parsed)
        (and (data-term-depth-bounded-p :term (car parsed) depth)
             (data-term-depth-bounded-p :terms (cdr parsed) depth)))))

(local
 (defun related-term-induction (kind parsed source depth)
   (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
   (if (eq kind :term)
       (cond ((or (atom parsed) (equal (car parsed) boymoo-compiler::*quote-name*)) (list source depth))
             ((consp (car parsed))
              (list (related-term-induction :term (caddar parsed) (caddar source) (1+ depth))
                    (related-term-induction :terms (cdr parsed) (cdr source) (1+ depth))))
             (t (related-term-induction :terms (cdr parsed) (cdr source) (1+ depth))))
     (if (atom parsed)
         (list source depth)
       (list (related-term-induction :term (car parsed) (car source) depth)
             (related-term-induction :terms (cdr parsed) (cdr source) depth))))))

(local
 (defthm lambda-name-fits-storage
   (data-symbol-storage-input-p "COMMON-LISP::LAMBDA")))

(local
 (defthm related-term-quotes-have-bindings
   (implies (and (if (eq kind :term) (data-source-term-agrees-p parsed source bindings)
                   (data-source-terms-agree-p parsed source bindings))
                 (< 0 (data-term-quote-count kind parsed text)))
            (assoc-equal text bindings))
   :rule-classes nil
   :hints (("Goal" :induct (related-term-induction kind parsed source 0)
                   :in-theory (disable data-source-symbols-agree-p boymoo-compiler::declaration-list)))))

(defthmd data-related-term-quote-has-source-binding
  (implies (and (data-source-term-agrees-p parsed source bindings)
                (< 0 (data-term-quote-count :term parsed text)))
           (assoc-equal text bindings))
  :hints (("Goal" :use ((:instance related-term-quotes-have-bindings (kind :term)))
                  :in-theory (disable data-source-term-agrees-p data-term-quote-count))))

(local
 (defthm related-terms-fit-storage
   (implies (and (if (eq kind :term)
                     (data-source-term-agrees-p parsed source bindings)
                   (data-source-terms-agree-p parsed source bindings))
                 (data-term-depth-bounded-p kind parsed depth)
                 (data-quote-spellings-p bindings witnesses))
            (and (data-term-storage-input-p kind parsed depth)
                 (data-term-constant-keys-p kind parsed depth)))
   :rule-classes nil
   :hints (("Goal" :induct (related-term-induction kind parsed source depth)
                   :in-theory (disable data-quote-spellings-p data-source-symbols-agree-p
                                       data-formals-storage-input-p boymoo-compiler::declaration-list)))))

(defthmd data-related-term-fits-storage
  (implies (and (data-source-term-agrees-p parsed source bindings)
                (data-term-depth-bounded-p :term parsed depth)
                (data-quote-spellings-p bindings witnesses))
           (and (data-term-storage-input-p :term parsed depth)
                (data-term-constant-keys-p :term parsed depth)))
  :hints (("Goal" :use ((:instance related-terms-fit-storage (kind :term)))
                  :in-theory (disable data-source-term-agrees-p data-term-depth-bounded-p
                                      data-quote-spellings-p data-term-storage-input-p data-term-constant-keys-p))))
