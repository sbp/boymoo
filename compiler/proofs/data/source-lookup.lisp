(in-package "BOYMOO-PROOFS")

(include-book "program-spelling")
(include-book "symbol-identity")

(logic)
(set-verify-guards-eagerness 0)

(defun data-canonical-source-name-p (text symbol)
  (and (symbolp symbol) (data-atom-spells-value-p text symbol)))

(local
 (in-theory (disable boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                     data-symbol-spelling-p data-source-symbol-agrees-p length)))

(defthmd data-canonical-source-names-have-exact-equality
  (implies (and (data-canonical-source-name-p left first) (data-canonical-source-name-p right second))
           (iff (equal left right) (equal first second)))
  :hints (("Goal" :use ((:instance data-canonical-symbol-spellings-are-unique
                                   (left-split (boymoo-compiler::symbol-separator left))
                                   (right-split (boymoo-compiler::symbol-separator right))
                                   (package (symbol-package-name first)) (name (symbol-name first)))
                        (:instance data-one-symbol-spelling-cannot-denote-two-source-symbols (text left))
                        (:instance data-canonical-symbol-denotes-source-symbol
                                   (text left) (split (boymoo-compiler::symbol-separator left)) (symbol first))
                        (:instance data-canonical-symbol-denotes-source-symbol
                                   (text right) (split (boymoo-compiler::symbol-separator right)) (symbol second))))))

(local
 (defthm canonical-source-name-is-a-string-and-symbol
   (implies (data-canonical-source-name-p text symbol) (and (stringp text) (symbolp symbol)))
   :rule-classes :forward-chaining))

(defun data-definition-heads-spelled-p (items definitions)
  (if (atom items)
      (and (null items) (null definitions))
    (and (consp definitions) (data-canonical-source-name-p (caar items) (caar definitions))
         (data-definition-heads-spelled-p (cdr items) (cdr definitions)))))

(defun data-lookup-heads-spelled-p (lines sources)
  (if (atom lines)
      (and (null lines) (null sources))
    (and (consp sources)
         (case (caar sources)
           (:define (data-definition-heads-spelled-p (cddar lines) (caddar sources)))
           (:attach (and (data-canonical-source-name-p (cadar lines) (cadar sources))
                         (data-canonical-source-name-p (caddar lines) (caddar sources))))
           (otherwise t))
         (data-lookup-heads-spelled-p (cdr lines) (cdr sources)))))

(defun data-source-file-definitions (sources)
  (if (atom sources)
      nil
    (if (eq (caar sources) :define)
        (append (caddar sources) (data-source-file-definitions (cdr sources)))
      (data-source-file-definitions (cdr sources)))))

(defun data-source-file-attachments (sources)
  (if (atom sources)
      nil
    (if (eq (caar sources) :attach)
        (cons (list (cadar sources) (caddar sources)) (data-source-file-attachments (cdr sources)))
      (data-source-file-attachments (cdr sources)))))

(defun data-source-program-from-lines (sources visible hidden)
  (boymoo-model::core-program (data-source-file-definitions sources)
                             (data-source-file-attachments sources) visible hidden))

(local
 (in-theory (disable data-canonical-source-name-p data-source-term-agrees-p data-source-symbols-agree-p
                     data-term-depth-bounded-p data-protected-name-p boymoo-compiler::declaration-list)))

(local
 (defthm latest-related-definition-on-one-line
   (implies (and (data-source-definitions-spelled-p items definitions bindings)
                 (data-definition-heads-spelled-p items definitions)
                 (data-canonical-source-name-p query symbol))
            (data-source-definition-agrees-p (assoc-equal query items) (assoc-equal symbol definitions) bindings))
   :hints (("Goal" :induct (data-source-definitions-spelled-p items definitions bindings))
           ("Subgoal *1/3" :use ((:instance data-canonical-source-names-have-exact-equality
                                            (left query) (right (caar items)) (first symbol)
                                            (second (caar definitions))))))))

(local
 (defthm definition-assoc-is-present-exactly-for-listed-name
   (implies (stringp query)
            (iff (assoc-equal query items) (member-equal query (strip-cars items))))))

(local
 (defthm reversed-unique-definitions-have-the-same-association
   (implies (and (stringp query) (no-duplicatesp-equal (strip-cars items)))
            (equal (assoc-equal query (boymoo-compiler::reverse-onto items tail))
                   (or (assoc-equal query items) (assoc-equal query tail))))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto items tail)))))

(local
 (defthm source-definition-lines-form-an-alist
   (implies (data-source-definitions-spelled-p items definitions bindings)
            (alistp definitions))
   :rule-classes :forward-chaining
   :hints (("Goal" :induct (data-source-definitions-spelled-p items definitions bindings)))))

(local
 (defthm assoc-of-definition-lists-appended
   (implies (alistp first)
            (equal (assoc-equal query (append first rest))
                   (or (assoc-equal query first) (assoc-equal query rest))))
   :hints (("Goal" :induct (append first rest)))))

(local
 (defthm nonempty-related-definitions-have-equal-presence
   (implies (data-source-definition-agrees-p parsed definition bindings)
            (iff parsed definition))
   :rule-classes nil))

(local
 (defthm absent-definitions-agree
   (data-source-definition-agrees-p nil nil bindings)))

(local
 (in-theory (disable data-source-definition-agrees-p data-source-definitions-spelled-p
                     data-definition-heads-spelled-p boymoo-compiler::reverse-onto)))

(defthmd data-latest-definition-agrees-with-source-file
  (implies (and (data-source-lines-spelled-p lines sources bindings entry target)
                (data-lookup-heads-spelled-p lines sources) (data-canonical-source-name-p query symbol)
                (not (assoc-equal query boymoo-compiler::*jets*)))
           (data-source-definition-agrees-p
            (data-latest-definition query lines)
            (boymoo-model::core-definition symbol (data-source-program-from-lines sources visible hidden))
            bindings))
  :hints (("Goal" :induct (data-source-lines-spelled-p lines sources bindings entry target))
          ("Subgoal *1/7" :use ((:instance latest-related-definition-on-one-line
                                           (items (cddar lines)) (definitions (caddar sources)))
                                (:instance nonempty-related-definitions-have-equal-presence
                                           (parsed (assoc-equal query (cddar lines)))
                                           (definition (assoc-equal symbol (caddar sources)))))
                          :in-theory (disable latest-related-definition-on-one-line))))

(defthmd data-latest-attachment-agrees-with-source-file
  (let ((source-attachment
         (boymoo-model::core-attachment symbol (data-source-program-from-lines sources visible hidden)))
        (written-target (data-latest-attachment query lines)))
    (implies (and (data-source-lines-spelled-p lines sources bindings entry target)
                  (data-lookup-heads-spelled-p lines sources) (data-canonical-source-name-p query symbol))
             (and (iff written-target source-attachment)
                  (implies written-target
                           (and (data-canonical-source-name-p written-target (cadr source-attachment))
                                (data-source-symbol-agrees-p written-target (cadr source-attachment)))))))
  :hints (("Goal" :induct (data-source-lines-spelled-p lines sources bindings entry target))
          ("Subgoal *1/7" :use ((:instance data-canonical-source-names-have-exact-equality
                                           (left query) (right (cadar lines)) (first symbol) (second (cadar sources)))))))

(defthmd data-checked-text-index-arity-is-source-arity
  (implies (and (data-program-spans-p text events lines)
                (data-source-lines-spelled-p lines sources bindings nil nil)
                (data-quote-spellings-p bindings witnesses)
                (data-lookup-heads-spelled-p lines sources) (data-canonical-source-name-p query symbol)
                (not (assoc-equal query boymoo-compiler::*jets*)))
           (let* ((source (data-source-program-from-lines sources visible hidden))
                  (parsed (boymoo-compiler::read-program text))
                  (arities (mv-nth 1 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))))
             (equal (boymoo-compiler::index-get query arities)
                    (data-source-arity (boymoo-model::core-definition symbol source)))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        (:instance data-latest-definition-agrees-with-source-file (entry nil) (target nil))
                        (:instance data-index-arity-for-source-definition (name symbol) (constants bindings)
                                   (program (data-source-program-from-lines sources visible hidden))))
                  :in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines
                                      boymoo-compiler::index-get boymoo-model::core-definition
                                      data-source-program-from-lines data-source-arity data-latest-definition
                                      data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p
                                      data-lookup-heads-spelled-p data-indexable-lines-p
                                      data-program-storage-input-p data-program-constant-keys-p
                                      data-package-lines-storage-input-p))))

(defthmd data-checked-text-index-attachment-is-source-attachment
  (implies (and (data-program-spans-p text events lines)
                (data-source-lines-spelled-p lines sources bindings nil nil)
                (data-quote-spellings-p bindings witnesses)
                (data-lookup-heads-spelled-p lines sources) (data-canonical-source-name-p query symbol))
           (let* ((source (data-source-program-from-lines sources visible hidden))
                  (source-attachment (boymoo-model::core-attachment symbol source))
                  (parsed (boymoo-compiler::read-program text))
                  (attachments (mv-nth 2 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
                  (written-target (boymoo-compiler::index-get query attachments)))
             (and (iff written-target source-attachment)
                  (implies source-attachment
                           (and (data-canonical-source-name-p written-target (cadr source-attachment))
                                (data-source-symbol-agrees-p written-target (cadr source-attachment)))))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        (:instance data-latest-attachment-agrees-with-source-file (entry nil) (target nil))
                        (:instance data-index-lines-latest-attachment
                                   (definitions nil) (arities nil) (attachments nil) (sources nil)
                                   (packages nil) (entry nil) (target nil)))
                  :in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines
                                      boymoo-compiler::index-get boymoo-model::core-attachment
                                      data-source-program-from-lines data-latest-attachment
                                      data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p
                                      data-lookup-heads-spelled-p data-indexable-lines-p
                                      data-program-storage-input-p data-program-constant-keys-p
                                      data-package-lines-storage-input-p))))
