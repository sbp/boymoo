(in-package "BOYMOO-PROOFS")

(include-book "term-spelling")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set data-table-p
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                     boymoo-compiler::decode-part data-symbol-storage-input-p
                     data-source-term-agrees-p data-source-symbols-agree-p char length)))

(local
 (defthm related-symbol-text-has-its-separator
   (implies (data-source-symbol-agrees-p text symbol)
            (and (stringp text) (boymoo-compiler::symbol-separator text)
                 (data-symbol-storage-input-p text)))
   :rule-classes ((:forward-chaining :trigger-terms ((data-source-symbol-agrees-p text symbol))))
   :hints (("Goal" :use ((:instance data-related-source-symbol-fits-storage))
                   :in-theory (disable data-related-source-symbol-fits-storage)))))

(local (in-theory (disable data-source-symbol-agrees-p)))

(local
 (defthm related-formals-are-a-true-list
   (implies (data-source-symbols-agree-p formals symbols) (true-listp formals))
   :rule-classes :forward-chaining
   :hints (("Goal" :induct (data-source-symbols-agree-p formals symbols)
                   :in-theory (enable data-source-symbols-agree-p)))))

(defun data-source-definitions-spelled-p (parsed definitions bindings)
  (if (atom parsed)
      (and (null parsed) (null definitions))
    (let ((definition (car parsed)))
      (and (consp definitions) (consp (cddr definition)) (null (cdddr definition))
           (not (data-protected-name-p (car definition)))
           (data-source-definition-agrees-p definition (car definitions) bindings)
           (data-term-depth-bounded-p :term (caddr definition) 0)
           (data-source-definitions-spelled-p (cdr parsed) (cdr definitions) bindings)))))

(local
 (defun index-definition-shapes-p (items)
   (if (atom items)
       (null items)
     (and (data-indexable-definition-p (car items)) (index-definition-shapes-p (cdr items))))))

(local
 (defthm spelled-definitions-have-indexable-shapes
   (implies (data-source-definitions-spelled-p parsed definitions bindings)
            (index-definition-shapes-p parsed))
   :rule-classes :forward-chaining
   :hints (("Goal" :induct (data-source-definitions-spelled-p parsed definitions bindings)
                   :in-theory (disable boymoo-compiler::declaration-list data-term-depth-bounded-p)))))

(local
 (defthm spelled-definitions-fit-storage
   (implies (and (data-source-definitions-spelled-p parsed definitions bindings)
                 (data-quote-spellings-p bindings witnesses))
            (and (data-definitions-storage-input-p parsed) (data-definition-constant-keys-p parsed)))
   :rule-classes ((:forward-chaining :trigger-terms ((data-source-definitions-spelled-p parsed definitions bindings)
                                                    (data-quote-spellings-p bindings witnesses))))
   :hints (("Goal" :induct (data-source-definitions-spelled-p parsed definitions bindings)
                   :in-theory (disable data-quote-spellings-p data-term-depth-bounded-p
                                       data-term-storage-input-p data-term-constant-keys-p
                                       data-protected-name-p
                                       data-formals-storage-input-p boymoo-compiler::declaration-list))
           ("Subgoal *1/3"
            :use ((:instance data-related-term-fits-storage (parsed (caddar parsed))
                             (source (caddar definitions)) (depth 0)))))))

(local
 (defthm reversing-keeps-definition-shapes
   (implies (and (index-definition-shapes-p items) (index-definition-shapes-p tail))
            (index-definition-shapes-p (boymoo-compiler::reverse-onto items tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto items tail)
                   :in-theory (disable data-indexable-definition-p)))))

(local
 (defthm definition-names-of-reverse
   (equal (strip-cars (boymoo-compiler::reverse-onto items tail))
          (boymoo-compiler::reverse-onto (strip-cars items) (strip-cars tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto items tail)))))

(local
 (defthm membership-of-reverse
   (iff (member-equal key (boymoo-compiler::reverse-onto items tail))
        (or (member-equal key items) (member-equal key tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto items tail)))))

(local
 (defun no-shared-names-p (items tail)
   (or (atom items) (and (not (member-equal (car items) tail)) (no-shared-names-p (cdr items) tail)))))

(local
 (defthm no-shared-names-with-nil
   (no-shared-names-p items nil)))

(local
 (defthm no-shared-names-when-one-name-is-added
   (equal (no-shared-names-p items (cons name tail))
          (and (not (member-equal name items)) (no-shared-names-p items tail)))))

(local
 (defthm reversing-keeps-distinct-names
   (implies (and (no-duplicatesp-equal items) (no-duplicatesp-equal tail) (no-shared-names-p items tail))
            (no-duplicatesp-equal (boymoo-compiler::reverse-onto items tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto items tail)))))

(local
 (defun definition-names-available-p (items seen)
   (or (atom items)
       (and (not (boymoo-compiler::index-get (caar items) seen))
            (definition-names-available-p (cdr items) seen)))))

(local
 (defthm definition-names-available-in-empty-table
   (definition-names-available-p items nil)))

(local
 (defthm unrelated-definition-names-stay-available
   (implies (and (index-definition-shapes-p items) (data-table-p seen 12) (stringp name)
                 (not (member-equal name (strip-cars items))))
            (equal (definition-names-available-p items (boymoo-compiler::index-set name t seen))
                   (definition-names-available-p items seen)))))

(local
 (defthm distinct-unseen-definitions-are-indexable
   (implies (and (index-definition-shapes-p items) (no-duplicatesp-equal (strip-cars items))
                 (data-table-p seen 12) (definition-names-available-p items seen))
            (data-indexable-definitions-p items seen))
   :hints (("Goal" :induct (data-indexable-definitions-p items seen)))))

(local
 (defthm spelled-definitions-are-indexable-in-line-order
   (implies (and (data-source-definitions-spelled-p parsed definitions bindings)
                 (no-duplicatesp-equal (strip-cars parsed)))
            (data-indexable-definitions-p (boymoo-compiler::reverse-onto parsed nil) nil))
   :rule-classes ((:forward-chaining :trigger-terms ((data-source-definitions-spelled-p parsed definitions bindings)
                                                    (no-duplicatesp-equal (strip-cars parsed)))))
   :hints (("Goal" :in-theory (disable data-indexable-definitions-p data-source-definitions-spelled-p
                                       boymoo-compiler::reverse-onto)))))

; A source line carries ACL2 data. The two line lists are in reverse
; file order, with the definitions and imports on each line in order.
(defun data-source-line-spelled-p (line source bindings)
  (case (car source)
    (:define
     (and (equal (car line) "define") (consp (cddr line))
          (data-parsed-datum-spells-value-p :datum (cadr line) (cadr source) nil)
          (data-source-definitions-spelled-p (cddr line) (caddr source) bindings)
          (no-duplicatesp-equal (strip-cars (cddr line)))))
    (:attach
     (and (equal (car line) "attach") (consp (cddr line)) (null (cdddr line))
          (data-source-symbol-agrees-p (cadr line) (cadr source))
          (data-source-symbol-agrees-p (caddr line) (caddr source))
          (not (data-protected-name-p (cadr line)))
          (not (equal (caddr line) boymoo-compiler::*if-name*))))
    (:package
     (and (equal (car line) (if (cadddr source) "package" "hidden-package"))
          (consp (cddr line)) (null (cdddr line))
          (stringp (cadr source))
          (data-atom-spells-value-p (cadr line) (cadr source))
          (or (equal (caddr line) boymoo-compiler::*nil-name*) (consp (caddr line)))
          (data-source-symbols-agree-p
           (boymoo-compiler::declaration-list (caddr line)) (caddr source))))
    (:entry
     (and (equal (car line) "entry") (null (cddr line))
          (data-source-symbol-agrees-p (cadr line) (cadr source))))
    (:target (and (eq (cadr source) :linux) (equal line '("target" "linux"))))
    (otherwise nil)))

(defun data-source-lines-spelled-p (lines sources bindings entry target)
  (if (atom lines)
      (and (null lines) (null sources))
    (and (consp sources) (data-source-line-spelled-p (car lines) (car sources) bindings)
         (case (caar sources)
           (:entry (and (not entry) (data-source-lines-spelled-p (cdr lines) (cdr sources)
                                                                 bindings (cadar lines) target)))
           (:target (and (not target) (data-source-lines-spelled-p (cdr lines) (cdr sources)
                                                                   bindings entry :linux)))
           (otherwise (data-source-lines-spelled-p (cdr lines) (cdr sources) bindings entry target))))))

(local
 (defthm spelled-definition-quotes-have-source-bindings
   (implies (and (data-source-definitions-spelled-p items definitions bindings)
                 (< 0 (data-definition-quote-count items text)))
            (assoc-equal text bindings))
   :rule-classes nil
   :hints (("Goal" :induct (data-source-definitions-spelled-p items definitions bindings)
                   :in-theory (disable data-term-quote-count data-term-depth-bounded-p))
           ("Subgoal *1/3" :use ((:instance data-related-term-quote-has-source-binding
                                            (parsed (caddar items)) (source (caddar definitions))))))))

(defthmd data-related-program-quote-has-source-binding
  (implies (and (data-source-lines-spelled-p lines sources bindings entry target)
                (< 0 (data-program-quote-count lines text)))
           (assoc-equal text bindings))
  :hints (("Goal" :induct (data-source-lines-spelled-p lines sources bindings entry target)
                  :in-theory (disable data-definition-quote-count data-source-definitions-spelled-p
                                      data-parsed-datum-spells-value-p data-atom-spells-value-p
                                      data-protected-name-p boymoo-compiler::declaration-list))
          ("Subgoal *1/7" :use ((:instance spelled-definition-quotes-have-source-bindings
                                           (items (cddar lines)) (definitions (caddar sources)))))))

(defthm data-spelled-package-name-decodes
  (implies (and (stringp name) (data-atom-spells-value-p text name))
           (and (stringp text) (equal (char text 0) #\")
                (equal (boymoo-compiler::decode-part text 0 (length text)) name)))
  :rule-classes ((:forward-chaining :trigger-terms ((data-atom-spells-value-p text name))))
  :hints (("Goal" :use ((:instance data-decode-canonical-delimited-text
                                   (start 0) (end (length text)) (characters (coerce name 'list))))
                  :in-theory (disable data-delimited-text-p))))

(local
 (in-theory (disable data-source-definitions-spelled-p data-quote-spellings-p
                     data-indexable-definitions-p boymoo-compiler::reverse-onto
                     data-parsed-datum-spells-value-p data-atom-spells-value-p data-protected-name-p
                     data-term-storage-input-p data-term-constant-keys-p
                     data-definitions-storage-input-p data-definition-constant-keys-p
                     data-formals-storage-input-p data-datum-storage-input-p data-datum-token-keys-p
                     boymoo-compiler::declaration-list)))

(local
 (defthm spelled-rulers-fit-storage
   (implies (data-parsed-datum-spells-value-p :datum parsed rulers nil)
            (and (data-datum-storage-input-p :datum parsed) (data-datum-token-keys-p :datum parsed)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use ((:instance data-parsed-datum-spelling-fits-storage
                                    (kind :datum) (value rulers) (after-item nil)))))))

(local
 (defthm two-symbol-tokens-fit-formal-storage
   (implies (and (consp (cdr inputs)) (null (cddr inputs))
                 (data-symbol-storage-input-p (car inputs)) (data-symbol-storage-input-p (cadr inputs)))
            (data-formals-storage-input-p inputs))
   :hints (("Goal" :in-theory (enable data-formals-storage-input-p)))))

(local
 (defthm one-symbol-token-fits-formal-storage
   (implies (and (null (cdr inputs)) (data-symbol-storage-input-p (car inputs)))
            (data-formals-storage-input-p inputs))
   :hints (("Goal" :in-theory (enable data-formals-storage-input-p)))))

(defthmd data-source-lines-spelling-gives-front-pass-inputs
  (implies (and (data-source-lines-spelled-p lines sources bindings entry target)
                (data-quote-spellings-p bindings witnesses))
           (and (data-indexable-lines-p lines entry target)
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-package-lines-storage-input-p (data-package-line-list lines))))
  :hints (("Goal" :induct (data-source-lines-spelled-p lines sources bindings entry target))))

(local
 (defthm package-storage-inputs-are-closed-under-reversal
   (implies (and (data-package-lines-storage-input-p lines) (data-package-lines-storage-input-p tail))
            (data-package-lines-storage-input-p (boymoo-compiler::reverse-onto lines tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto lines tail)
                   :in-theory (enable boymoo-compiler::reverse-onto)))))

(defthmd data-read-program-gives-source-front-pass-inputs
  (implies (and (data-program-spans-p text events lines)
                (data-source-lines-spelled-p lines sources bindings nil nil)
                (data-quote-spellings-p bindings witnesses))
           (let* ((parsed (boymoo-compiler::read-program text))
                  (packages (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))))
             (and (equal parsed lines) (data-indexable-lines-p parsed nil nil)
                  (data-program-storage-input-p parsed) (data-program-constant-keys-p parsed)
                  (data-package-lines-storage-input-p packages))))
  :hints (("Goal" :use (data-read-program-from-spans
                        (:instance data-source-lines-spelling-gives-front-pass-inputs (entry nil) (target nil))
                        (:instance data-index-lines-package-order
                                   (definitions nil) (arities nil) (attachments nil) (sources nil)
                                   (packages nil) (entry nil) (target nil)))
                  :in-theory (disable data-source-lines-spelled-p data-program-spans-p
                                      boymoo-compiler::read-program boymoo-compiler::index-lines
                                      data-indexable-lines-p data-program-constant-keys-p
                                      data-program-storage-input-p data-package-lines-storage-input-p))))
