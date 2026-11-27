(in-package "BOYMOO-PROOFS")

(include-book "program-spelling")
(include-book "packages")

(logic)
(set-verify-guards-eagerness 0)

(defun data-source-package-lines (sources)
  (if (atom sources)
      nil
    (if (eq (caar sources) :package)
        (cons (car sources) (data-source-package-lines (cdr sources)))
      (data-source-package-lines (cdr sources)))))

(defun data-source-package-names (sources)
  (if (atom sources)
      nil
    (cons (cadar sources) (data-source-package-names (cdr sources)))))

(defun data-source-package-visible-in-lines-p (name sources)
  (if (atom sources)
      nil
    (or (and (equal name (cadar sources)) (cadddr (car sources)))
        (data-source-package-visible-in-lines-p name (cdr sources)))))

; The relation carries decoded names and ordered ACL2 import symbols.
(defun data-package-lines-match-source-p (lines sources)
  (if (atom lines)
      (and (null lines) (null sources))
    (and (consp sources) (eq (caar sources) :package)
         (equal (data-package-line-name (car lines)) (cadar sources))
         (equal (caar lines) (if (cadddr (car sources)) "package" "hidden-package"))
         (data-source-symbols-agree-p (boymoo-compiler::declaration-list (caddar lines)) (caddar sources))
         (data-package-lines-match-source-p (cdr lines) (cdr sources)))))

(local
 (in-theory (disable data-source-definitions-spelled-p data-source-symbol-agrees-p data-source-symbols-agree-p
                     data-parsed-datum-spells-value-p data-atom-spells-value-p data-protected-name-p
                     boymoo-compiler::decode-part boymoo-compiler::declaration-list length)))

(defthmd data-filtered-package-lines-match-source
  (implies (data-source-lines-spelled-p lines sources bindings entry target)
           (data-package-lines-match-source-p (data-package-line-list lines) (data-source-package-lines sources)))
  :hints (("Goal" :induct (data-source-lines-spelled-p lines sources bindings entry target))))

(local
 (defun reverse-package-lines-induction (lines sources tail source-tail)
   (if (atom lines)
       (list sources tail source-tail)
     (reverse-package-lines-induction (cdr lines) (cdr sources) (cons (car lines) tail)
                                      (cons (car sources) source-tail)))))

(defthmd data-reversing-package-lines-keeps-source-agreement
  (implies (and (data-package-lines-match-source-p lines sources) (data-package-lines-match-source-p tail source-tail))
           (data-package-lines-match-source-p (boymoo-compiler::reverse-onto lines tail)
                                               (boymoo-compiler::reverse-onto sources source-tail)))
  :hints (("Goal" :induct (reverse-package-lines-induction lines sources tail source-tail)
                  :in-theory (disable data-package-line-name))))

(defthmd data-index-package-lines-match-source-in-file-order
  (implies (and (data-program-spans-p text events lines)
                (data-source-lines-spelled-p lines sources bindings nil nil)
                (data-quote-spellings-p bindings witnesses))
           (let ((parsed (boymoo-compiler::read-program text)))
             (data-package-lines-match-source-p
              (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
              (boymoo-compiler::reverse-onto (data-source-package-lines sources) nil))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        (:instance data-filtered-package-lines-match-source (entry nil) (target nil))
                        (:instance data-index-lines-package-order
                                   (definitions nil) (arities nil) (attachments nil) (sources nil)
                                   (packages nil) (entry nil) (target nil))
                        (:instance data-reversing-package-lines-keeps-source-agreement
                                   (lines (data-package-line-list lines)) (sources (data-source-package-lines sources))
                                   (tail nil) (source-tail nil)))
                  :in-theory (disable boymoo-compiler::index-lines boymoo-compiler::read-program
                                      boymoo-compiler::reverse-onto data-source-lines-spelled-p data-program-spans-p
                                      data-quote-spellings-p data-indexable-lines-p data-package-line-list
                                      data-source-package-lines data-program-storage-input-p
                                      data-program-constant-keys-p data-package-lines-storage-input-p))))

(defthmd data-package-line-names-and-visibility-match-source
  (implies (data-package-lines-match-source-p lines sources)
           (and (equal (data-package-line-names lines) (data-source-package-names sources))
                (iff (data-package-visible-in-lines-p query lines)
                     (data-source-package-visible-in-lines-p query sources))))
  :hints (("Goal" :induct (data-package-lines-match-source-p lines sources)
                  :in-theory (disable data-package-line-name))))

(defthmd data-package-numbers-follow-source-first-declarations
  (let* ((names (data-source-package-names sources))
         (first (data-first-package-names names nil)))
    (implies (and (data-package-lines-match-source-p lines sources) (data-package-names-p names))
             (equal (boymoo-compiler::data-package-numbers lines 0 nil)
                    (data-binding-index (boymoo-compiler::reverse-onto (data-number-rows first 0) nil)))))
  :hints (("Goal" :use (data-package-line-names-and-visibility-match-source
                        (:instance data-package-numbers-first-order (package-lines lines)))
                  :in-theory (disable boymoo-compiler::data-package-numbers
                                      data-package-line-names data-package-lines-match-source-p))))
