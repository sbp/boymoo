(in-package "BOYMOO-PROOFS")

(include-book "attachment-graph")
(include-book "source-lookup")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defconst *source-primitive-symbols*
   '(if acl2-numberp acl2::bad-atom<= acl2::binary-* acl2::binary-+
        acl2::unary-- acl2::unary-/ < car cdr char-code characterp code-char complex
        complex-rationalp coerce cons consp denominator equal imagpart integerp
        acl2::intern-in-package-of-symbol numerator acl2::pkg-imports acl2::pkg-witness
        rationalp realpart stringp symbol-name acl2::symbol-package-name symbolp)))

(local
 (defconst *compiler-protected-texts*
   (cons boymoo-compiler::*if-name* (strip-cars boymoo-compiler::*primitives*))))

(local
 (defun canonical-attachment-names-p (names symbols)
   (if (atom names)
       (and (null names) (null symbols))
     (and (consp symbols) (data-canonical-source-name-p (car names) (car symbols))
          (canonical-attachment-names-p (cdr names) (cdr symbols))))))

(local
 (defthm source-primitives-have-the-protected-texts
   (canonical-attachment-names-p *compiler-protected-texts* *source-primitive-symbols*)))

(local
 (in-theory (disable data-canonical-source-name-p data-source-symbol-agrees-p
                     boymoo-compiler::index-lines boymoo-compiler::index-get
                     data-source-program-from-lines data-indexable-lines-p)))

(local
 (defthm canonical-membership-gives-text-membership
   (implies (and (canonical-attachment-names-p texts symbols)
                 (data-canonical-source-name-p text symbol) (member-equal symbol symbols))
            (member-equal text texts))
   :hints (("Goal" :induct (canonical-attachment-names-p texts symbols))
           ("Subgoal *1/3" :use ((:instance data-canonical-source-names-have-exact-equality
                                            (left text) (right (car texts)) (first symbol) (second (car symbols))))))))

(local
 (defthm membership-in-protected-texts-is-protected
   (iff (member-equal text *compiler-protected-texts*) (data-protected-name-p text))))

(local
 (defthm absent-from-source-primitives-means-no-primitive-call
   (implies (not (member-equal symbol *source-primitive-symbols*))
            (not (boymoo-model::core-primitive symbol args program)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::core-primitive)
                                   (boymoo-model::core-visible-package-p boymoo-model::core-hidden-symbol-p))))))

(defthmd data-unprotected-canonical-name-has-no-source-primitive
  (implies (and (data-canonical-source-name-p text symbol) (not (data-protected-name-p text)))
           (not (boymoo-model::core-primitive symbol args program)))
  :hints (("Goal" :use ((:instance canonical-membership-gives-text-membership
                                   (texts *compiler-protected-texts*) (symbols *source-primitive-symbols*)))
                  :in-theory (disable data-protected-name-p canonical-membership-gives-text-membership))))

(local
 (defthm canonical-attachment-name-decodes-to-the-source-symbol
   (implies (data-canonical-source-name-p text symbol) (data-source-symbol-agrees-p text symbol))
   :hints (("Goal" :use ((:instance data-canonical-symbol-denotes-source-symbol
                                    (split (boymoo-compiler::symbol-separator text))))
                   :in-theory (e/d (data-canonical-source-name-p)
                                   (data-symbol-spelling-p boymoo-compiler::symbol-separator))))))

(local
 (defthm canonical-attachment-pairs-have-a-text-and-a-symbol
   (implies (data-canonical-source-name-p text symbol) (and (stringp text) (symbolp symbol)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-canonical-source-name-p)))))

(local
 (defthm indexed-edge-matches-the-latest-written-attachment
   (implies (and (data-indexable-lines-p lines nil nil) (stringp text))
            (equal (data-attachment-edge text
                                         (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
                   (data-latest-attachment text lines)))
   :hints (("Goal" :use ((:instance data-index-lines-latest-attachment
                                    (query text) (definitions nil) (arities nil) (attachments nil)
                                    (sources nil) (packages nil) (entry nil) (target nil))
                         (:instance data-latest-attachment-source-is-unprotected
                                    (name text) (entry nil) (target nil)))
                   :in-theory (disable data-latest-attachment data-protected-name-p)))))

(defthmd data-indexed-attachment-edge-agrees-with-source-step
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (edge (data-attachment-edge text (mv-nth 2 pass)))
         (program (data-source-program-from-lines sources visible hidden))
         (binding (boymoo-model::core-attachment symbol program)))
    (implies (and (data-indexable-lines-p lines nil nil) (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-lookup-heads-spelled-p lines sources) (data-canonical-source-name-p text symbol))
             (and (iff edge binding)
                  (implies edge (and (data-canonical-source-name-p edge (cadr binding))
                                     (not (boymoo-model::core-primitive symbol args program)))))))
  :hints (("Goal" :use ((:instance data-latest-attachment-agrees-with-source-file
                                   (query text) (entry nil) (target nil))
                        (:instance data-latest-attachment-source-is-unprotected
                                   (name text) (entry nil) (target nil))
                        (:instance data-unprotected-canonical-name-has-no-source-primitive
                                   (program (data-source-program-from-lines sources visible hidden))))
                  :in-theory (e/d (data-canonical-source-name-p)
                                 (boymoo-model::core-attachment data-attachment-edge
                                  data-latest-attachment data-protected-name-p
                                  data-source-lines-spelled-p data-lookup-heads-spelled-p
                                  data-symbol-spelling-p boymoo-compiler::symbol-separator)))))

; The text path fixes the number of positions. Each subsequent symbol
; is the target of the source model's effective attachment.
(defun data-source-symbols-on-attachment-path (path symbol program)
  (if (atom path)
      nil
    (cons symbol (data-source-symbols-on-attachment-path
                  (cdr path) (cadr (boymoo-model::core-attachment symbol program)) program))))

(local
 (in-theory (disable data-source-lines-spelled-p data-lookup-heads-spelled-p
                     data-attachment-edge data-attachment-path-p boymoo-model::core-attachment
                     data-latest-attachment indexed-edge-matches-the-latest-written-attachment
                     canonical-attachment-name-decodes-to-the-source-symbol)))

(defthmd data-indexed-terminal-path-agrees-with-source-calls
  (let* ((program (data-source-program-from-lines sources visible hidden))
         (attachments (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
         (symbols (data-source-symbols-on-attachment-path path symbol program)))
    (implies (and (data-indexable-lines-p lines nil nil) (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-lookup-heads-spelled-p lines sources) (data-canonical-source-name-p (car path) symbol)
                  (data-attachment-path-p path attachments))
             (and (data-source-symbols-agree-p path symbols)
                  (data-source-attachment-path-p symbols args program)
                  (data-canonical-source-name-p (data-attachment-terminal path) (data-attachment-terminal symbols))
                  (not (boymoo-model::core-attachment (data-attachment-terminal symbols) program)))))
  :hints (("Goal" :induct (data-source-symbols-on-attachment-path
                           path symbol (data-source-program-from-lines sources visible hidden))
                  :expand ((:free (attachments) (data-attachment-path-p path attachments))))
          ("Subgoal *1/2" :use ((:instance data-indexed-attachment-edge-agrees-with-source-step (text (car path)))
                                (:instance canonical-attachment-name-decodes-to-the-source-symbol
                                           (text (car path)))))))

(local
 (defthm source-walk-starts-with-the-source-name
   (implies (consp path)
            (equal (car (data-source-symbols-on-attachment-path path symbol program)) symbol))))

(local
 (defthm source-walk-has-the-length-of-the-text-path
   (equal (len (data-source-symbols-on-attachment-path path symbol program)) (len path))))

(local
 (in-theory (disable data-source-symbols-on-attachment-path data-attachment-walk
                     data-attachment-terminal data-indexed-attachments-acyclic-p
                     data-source-symbols-agree-p data-source-attachment-path-p
                     boymoo-model::core-call boymoo-compiler::resolve-attachments)))

(defthmd data-indexed-resolution-agrees-with-source-call
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass)) (names (mv-nth 3 pass))
         (resolved (boymoo-compiler::resolve-attachments names attachments nil (len names)))
         (text-path (data-attachment-walk query attachments names))
         (program (data-source-program-from-lines sources visible hidden))
         (symbol-path (data-source-symbols-on-attachment-path text-path symbol program))
         (terminal (data-attachment-terminal symbol-path)))
    (implies (and (data-indexable-lines-p lines nil nil) (data-indexed-attachments-acyclic-p lines)
                  (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-lookup-heads-spelled-p lines sources) (data-canonical-source-name-p query symbol)
                  (boymoo-model::core-attachment symbol program) (natp fuel))
             (and (data-canonical-source-name-p (boymoo-compiler::index-get query resolved) terminal)
                  (not (boymoo-model::core-attachment terminal program))
                  (equal (boymoo-model::core-call symbol args program (+ fuel (1- (len text-path))))
                         (boymoo-model::core-call terminal args program fuel)))))
  :hints (("Goal"
           :use ((:instance data-indexed-attachment-edge-agrees-with-source-step (text query))
                 (:instance data-indexed-attachment-edges-have-listed-sources (name query))
                 (:instance data-indexed-walk-is-terminal-and-gives-resolved-target (name query))
                 (:instance data-indexed-terminal-path-agrees-with-source-calls
                            (path (data-attachment-walk
                                   query
                                   (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                   (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))))
                 (:instance data-source-call-along-attachment-path
                            (path (data-source-symbols-on-attachment-path
                                   (data-attachment-walk
                                    query
                                    (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                    (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
                                   symbol (data-source-program-from-lines sources visible hidden)))
                            (program (data-source-program-from-lines sources visible hidden)))))))

(defthmd data-checked-text-resolves-source-attachment
  (let* ((parsed (boymoo-compiler::read-program text))
         (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass)) (names (mv-nth 3 pass))
         (resolved (boymoo-compiler::resolve-attachments names attachments nil (len names)))
         (text-path (data-attachment-walk query attachments names))
         (program (data-source-program-from-lines sources visible hidden))
         (terminal (data-attachment-terminal (data-source-symbols-on-attachment-path text-path symbol program))))
    (implies (and (data-program-spans-p text events lines)
                  (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-quote-spellings-p bindings witnesses) (data-lookup-heads-spelled-p lines sources)
                  (data-indexed-attachments-acyclic-p lines) (data-canonical-source-name-p query symbol)
                  (boymoo-model::core-attachment symbol program) (natp fuel))
             (and (data-canonical-source-name-p (boymoo-compiler::index-get query resolved) terminal)
                  (not (boymoo-model::core-attachment terminal program))
                  (equal (boymoo-model::core-call symbol args program (+ fuel (1- (len text-path))))
                         (boymoo-model::core-call terminal args program fuel)))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        data-indexed-resolution-agrees-with-source-call)
                  :in-theory (disable boymoo-compiler::read-program data-program-spans-p data-quote-spellings-p
                                      data-program-storage-input-p data-program-constant-keys-p
                                      data-package-lines-storage-input-p))))
