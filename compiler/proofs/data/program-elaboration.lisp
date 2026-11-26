(in-package "BOYMOO-PROOFS")

(include-book "elaboration")
(include-book "source-lookup")
(include-book "reader-witness")

(logic)
(set-verify-guards-eagerness 0)

(defun data-elaborate-definition-list (definitions packages bindings)
  (if (atom definitions)
      (mv (null definitions) nil)
    (let ((definition (car definitions)))
      (mv-let (name-ok name) (data-elaborate-symbol (car definition) packages)
        (mv-let (formals-ok formals)
          (data-elaborate-symbols (boymoo-compiler::declaration-list (cadr definition)) packages)
          (mv-let (body-ok body) (data-elaborate-term :term (caddr definition) packages bindings)
            (mv-let (rest-ok rest) (data-elaborate-definition-list (cdr definitions) packages bindings)
              (mv (and name-ok formals-ok body-ok rest-ok) (cons (list name formals body) rest)))))))))

(defun data-elaborate-line-candidate (line packages bindings)
  (let ((kind (car line)) (name (cadr line)))
    (cond ((equal kind "define")
           (mv-let (rulers-ok rulers) (if (consp name) (data-elaborate-symbols name packages)
                                       (data-elaborate-symbol name packages))
             (mv-let (definitions-ok definitions) (data-elaborate-definition-list (cddr line) packages bindings)
               (and rulers-ok definitions-ok (list :define rulers definitions)))))
          ((equal kind "attach")
           (mv-let (source-ok source) (data-elaborate-symbol name packages)
             (mv-let (target-ok target) (data-elaborate-symbol (caddr line) packages)
               (and source-ok target-ok (list :attach source target)))))
          ((or (equal kind "package") (equal kind "hidden-package"))
           (mv-let (imports-ok imports)
             (data-elaborate-symbols (boymoo-compiler::declaration-list (caddr line)) packages)
             (and imports-ok (stringp name)
                  (list :package (boymoo-compiler::decode-part name 0 (length name)) imports (equal kind "package")))))
          ((equal kind "entry")
           (mv-let (ok symbol) (data-elaborate-symbol name packages)
             (and ok (list :entry symbol))))
          ((equal kind "target") '(:target :linux))
          (t nil))))

; The source and lookup relations check each candidate as the parsed lines are traversed.
; Each entry or target line also checks the state of its directive.
(defun data-elaborate-program-lines (lines packages bindings entry target)
  (if (atom lines)
      (mv (null lines) nil)
    (let* ((line (car lines)) (source (data-elaborate-line-candidate line packages bindings))
           (kind (car source)))
      (if (and (data-source-line-spelled-p line source bindings)
               (data-lookup-heads-spelled-p (list line) (list source))
               (or (not (eq kind :entry)) (not entry))
               (or (not (eq kind :target)) (not target)))
          (mv-let (ok rest) (data-elaborate-program-lines
                             (cdr lines) packages bindings (if (eq kind :entry) (cadr line) entry)
                             (if (eq kind :target) :linux target))
            (mv ok (cons source rest)))
        (mv nil nil)))))

(local
 (in-theory (disable data-elaborate-line-candidate data-source-line-spelled-p
                     data-definition-heads-spelled-p data-canonical-source-name-p)))

(defthmd data-elaborated-program-lines-agree-with-text-and-lookup-heads
  (mv-let (ok sources) (data-elaborate-program-lines lines packages bindings entry target)
    (implies ok (and (data-source-lines-spelled-p lines sources bindings entry target)
                     (data-lookup-heads-spelled-p lines sources))))
  :hints (("Goal" :induct (data-elaborate-program-lines lines packages bindings entry target))))

(defun data-elaborate-program-text (text packages bindings)
  (mv-let (read-ok events lines) (data-infer-program-spans text)
    (if (not read-ok)
        (mv nil nil nil nil)
      (mv-let (ok sources) (data-elaborate-program-lines lines packages bindings nil nil)
        (mv ok events lines sources)))))

(local
 (in-theory (disable data-elaborate-program-lines data-infer-program-spans data-program-spans-p
                     data-source-lines-spelled-p data-lookup-heads-spelled-p)))

(defthmd data-elaborated-program-text-supplies-the-checked-source-relations
  (mv-let (ok events lines sources) (data-elaborate-program-text text packages bindings)
    (implies ok (and (data-program-spans-p text events lines)
                     (data-source-lines-spelled-p lines sources bindings nil nil)
                     (data-lookup-heads-spelled-p lines sources))))
  :hints (("Goal" :use (data-inferred-program-spans-validate
                        (:instance data-elaborated-program-lines-agree-with-text-and-lookup-heads
                                   (lines (mv-nth 2 (data-infer-program-spans text))) (entry nil) (target nil))))))
