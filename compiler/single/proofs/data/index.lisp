(in-package "BOYMOO-PROOFS")

(include-book "tables")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::symbol-separator data-table-p)))

(defun data-protected-name-p (name)
  (or (assoc-equal name boymoo-compiler::*primitives*)
      (equal name boymoo-compiler::*if-name*)))

(defun data-indexable-definition-p (definition)
  (let ((name (car definition))
        (formals (boymoo-compiler::declaration-list (cadr definition))))
    (and (stringp name) (boymoo-compiler::symbol-separator name)
         (consp (cddr definition)) (not (cdddr definition))
         (or (not formals) (consp formals))
         (not (data-protected-name-p name)))))

; These clauses require each executable check made during the index pass
; to succeed. The seen table belongs to one define line.
(defun data-indexable-definitions-p (items seen)
  (if (atom items)
      (null items)
    (let ((name (caar items)))
      (and (data-indexable-definition-p (car items))
           (if (assoc-equal name boymoo-compiler::*jets*)
               (data-indexable-definitions-p (cdr items) seen)
             (and (not (boymoo-compiler::index-get name seen))
                  (data-indexable-definitions-p
                   (cdr items)
                   (if (consp (cdr items)) (boymoo-compiler::index-set name t seen) seen))))))))

(defun data-definition-candidate (query items)
  (and (not (assoc-equal query boymoo-compiler::*jets*))
       (assoc-equal query items)))

(defun data-definition-arity (definition)
  (and definition (len (boymoo-compiler::declaration-list (cadr definition)))))

(local
 (defthm length-of-definition-formals
   (implies (data-indexable-definition-p definition)
            (equal (length (boymoo-compiler::declaration-list (cadr definition)))
                   (data-definition-arity definition)))))

(local
 (defthm length-of-nonstring
   (implies (not (stringp contents)) (equal (length contents) (len contents)))))

(defthm data-index-definition-line-table-p
  (implies (and (data-indexable-definitions-p items seen) (data-table-p arities 12))
           (data-table-p (mv-nth 1 (boymoo-compiler::index-definition-line
                                     items definitions arities seen)) 12))
  :hints (("Goal" :induct (boymoo-compiler::index-definition-line items definitions arities seen)
                  :in-theory (disable length))))

(defthmd data-index-definition-line-arity
  (implies (and (data-indexable-definitions-p items seen) (data-table-p arities 12)
                (stringp query))
           (equal (boymoo-compiler::index-get
                   query (mv-nth 1 (boymoo-compiler::index-definition-line
                                     items definitions arities seen)))
                  (or (boymoo-compiler::index-get query arities)
                      (data-definition-arity (data-definition-candidate query items)))))
  :hints (("Goal" :induct (boymoo-compiler::index-definition-line items definitions arities seen)
                  :in-theory (disable length))))

(defthmd data-index-definition-line-definition
  (implies (and (data-indexable-definitions-p items seen) (data-table-p arities 12)
                (stringp query))
           (equal (assoc-equal query (car (boymoo-compiler::index-definition-line
                                          items definitions arities seen)))
                  (if (boymoo-compiler::index-get query arities)
                      (assoc-equal query definitions)
                    (or (data-definition-candidate query items) (assoc-equal query definitions)))))
  :hints (("Goal" :induct (boymoo-compiler::index-definition-line items definitions arities seen)
                  :in-theory (disable length))))

(defun data-package-line-kind-p (line)
  (member-equal (car line) '("package" "hidden-package")))

(defun data-indexable-lines-p (lines entry target)
  (if (atom lines)
      (null lines)
    (let* ((line (car lines)) (kind (car line)) (name (cadr line)))
      (cond ((and (equal kind "define") (consp (cddr line)))
             (and (data-indexable-definitions-p (boymoo-compiler::reverse-onto (cddr line) nil) nil)
                  (data-indexable-lines-p (cdr lines) entry target)))
            ((equal kind "attach")
             (and (stringp name) (stringp (caddr line)) (not (consp (cdddr line)))
                  (not (data-protected-name-p name))
                  (not (equal (caddr line) boymoo-compiler::*if-name*))
                  (data-indexable-lines-p (cdr lines) entry target)))
            ((and (data-package-line-kind-p line) (stringp name)
                  (equal (char name 0) #\") (consp (cddr line)) (not (cdddr line))
                  (or (equal (caddr line) boymoo-compiler::*nil-name*) (consp (caddr line))))
             (data-indexable-lines-p (cdr lines) entry target))
            ((and (equal kind "entry") (not entry) (stringp name) (not (cddr line)))
             (data-indexable-lines-p (cdr lines) name target))
            ((and (not target) (equal line '("target" "linux")))
             (data-indexable-lines-p (cdr lines) entry :linux))
            (t nil)))))

; The reader supplies lines in reverse file order. The first match is
; the latest binding. An indexable line defines each of its names once.
(defun data-latest-definition (query lines)
  (if (atom lines)
      nil
    (or (and (equal (caar lines) "define")
             (data-definition-candidate query (boymoo-compiler::reverse-onto (cddar lines) nil)))
        (data-latest-definition query (cdr lines)))))

(defun data-latest-attachment (query lines)
  (if (atom lines)
      nil
    (let ((line (car lines)))
      (if (and (equal (car line) "attach") (equal query (cadr line)))
          (caddr line)
        (data-latest-attachment query (cdr lines))))))

(defun data-package-line-list (lines)
  (if (atom lines)
      nil
    (if (data-package-line-kind-p (car lines))
        (cons (car lines) (data-package-line-list (cdr lines)))
      (data-package-line-list (cdr lines)))))

(local
 (in-theory (disable boymoo-compiler::index-definition-line boymoo-compiler::reverse-onto
                     data-definition-candidate)))

(local
 (defthm data-index-definitions-arity-table
   (implies (and (data-indexable-definitions-p items nil) (data-table-p arities 12))
            (data-table-p (mv-nth 1 (boymoo-compiler::index-definitions items definitions arities)) 12))))

(defthmd data-index-lines-latest-arity
  (implies (and (data-indexable-lines-p lines entry target) (data-table-p arities 12) (stringp query))
           (equal (boymoo-compiler::index-get
                   query (mv-nth 1 (boymoo-compiler::index-lines
                                    lines definitions arities attachments sources packages entry target)))
                  (or (boymoo-compiler::index-get query arities)
                      (data-definition-arity (data-latest-definition query lines)))))
  :hints (("Goal" :induct (boymoo-compiler::index-lines
                            lines definitions arities attachments sources packages entry target)
                  :in-theory (enable data-index-definition-line-arity))))

(defthmd data-index-lines-latest-definition
  (implies (and (data-indexable-lines-p lines entry target) (data-table-p arities 12) (stringp query))
           (equal (assoc-equal query (car (boymoo-compiler::index-lines
                                          lines definitions arities attachments sources packages entry target)))
                  (if (boymoo-compiler::index-get query arities)
                      (assoc-equal query definitions)
                    (or (data-latest-definition query lines) (assoc-equal query definitions)))))
  :hints (("Goal" :induct (boymoo-compiler::index-lines
                            lines definitions arities attachments sources packages entry target)
                  :in-theory (enable data-index-definition-line-arity
                                     data-index-definition-line-definition))))

(defthmd data-index-lines-latest-attachment
  (implies (and (data-indexable-lines-p lines entry target) (data-table-p attachments 12) (stringp query))
           (equal (boymoo-compiler::index-get
                   query (mv-nth 2 (boymoo-compiler::index-lines
                                    lines definitions arities attachments sources packages entry target)))
                  (or (boymoo-compiler::index-get query attachments)
                      (data-latest-attachment query lines))))
  :hints (("Goal" :induct (boymoo-compiler::index-lines
                            lines definitions arities attachments sources packages entry target))))

(defthmd data-index-lines-attachment-sources
  (implies (and (data-indexable-lines-p lines entry target) (data-table-p attachments 12) (stringp query))
           (iff (member-equal query (mv-nth 3 (boymoo-compiler::index-lines
                                               lines definitions arities attachments sources packages entry target)))
                (or (member-equal query sources)
                    (and (not (boymoo-compiler::index-get query attachments))
                         (data-latest-attachment query lines)))))
  :hints (("Goal" :induct (boymoo-compiler::index-lines
                            lines definitions arities attachments sources packages entry target))))

(defthmd data-index-lines-attachment-table-p
  (implies (and (data-indexable-lines-p lines entry target) (data-table-p attachments 12))
           (data-table-p
            (mv-nth 2 (boymoo-compiler::index-lines
                        lines definitions arities attachments sources packages entry target)) 12))
  :hints (("Goal" :induct (boymoo-compiler::index-lines
                            lines definitions arities attachments sources packages entry target))))

(defthmd data-index-lines-package-order
  (implies (data-indexable-lines-p lines entry target)
           (equal (mv-nth 4 (boymoo-compiler::index-lines
                             lines definitions arities attachments sources packages entry target))
                  (boymoo-compiler::reverse-onto (data-package-line-list lines) packages)))
  :hints (("Goal" :induct (boymoo-compiler::index-lines
                            lines definitions arities attachments sources packages entry target)
                  :in-theory (enable boymoo-compiler::reverse-onto))))

(defun data-latest-arities (queries lines)
  (if (atom queries)
      nil
    (cons (cons (car queries) (data-definition-arity (data-latest-definition (car queries) lines)))
          (data-latest-arities (cdr queries) lines))))

(defthmd data-index-lines-arity-agreement
  (implies (and (string-listp queries) (data-indexable-lines-p lines nil nil))
           (proof-index-agrees-p
            (data-latest-arities queries lines)
            (mv-nth 1 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
  :hints (("Goal" :induct (data-latest-arities queries lines)
                  :in-theory (e/d (data-index-lines-latest-arity) (boymoo-compiler::index-lines)))))
