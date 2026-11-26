(in-package "BOYMOO-PROOFS")

(include-book "reader-acceptance")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-checked-index-definitions (items defs names seen)
  (if (atom items)
      (mv t defs names)
    (let* ((definition (car items))
           (name (car definition))
           (formals (boymoo-compiler::declaration-list (cadr definition))))
      (cond
       ((or (not (and (stringp name) (boymoo-compiler::symbol-separator name)))
            (not (and (consp (cddr definition)) (not (cdddr definition))))
            (and formals (atom formals))
            (assoc-equal name boymoo-compiler::*primitives*)
            (equal name boymoo-compiler::*if-name*))
        (mv nil nil nil))
       ((assoc-equal name boymoo-compiler::*jets*)
        (assembly-checked-index-definitions (cdr items) defs names seen))
       ((boymoo-compiler::index-get name seen) (mv nil nil nil))
       (t
        (let ((seen (if (consp (cdr items)) (boymoo-compiler::index-set name t seen) seen)))
          (if (boymoo-compiler::index-get name names)
              (assembly-checked-index-definitions (cdr items) defs names seen)
            (assembly-checked-index-definitions
             (cdr items) (cons definition defs)
             (boymoo-compiler::index-set name (length formals) names) seen))))))))

(defun assembly-checked-index-lines (lines defs names attachments sources packages entry target)
  (if (atom lines)
      (mv t defs names attachments sources packages entry target)
    (let* ((line (car lines))
           (word (car line))
           (name (cadr line)))
      (cond
       ((and (equal word "define") (consp (cddr line)))
        (mv-let (ok defs names)
          (assembly-checked-index-definitions
           (boymoo-compiler::reverse-onto (cddr line) nil) defs names nil)
          (if ok
              (assembly-checked-index-lines
               (cdr lines) defs names attachments sources packages entry target)
            (mv nil nil nil nil nil nil nil nil))))
       ((equal word "attach")
        (cond
         ((or (consp (cdddr line)) (not (stringp (caddr line))) (not (stringp name))
              (assoc-equal name boymoo-compiler::*primitives*) (equal name boymoo-compiler::*if-name*)
              (equal (caddr line) boymoo-compiler::*if-name*))
          (mv nil nil nil nil nil nil nil nil))
         ((boymoo-compiler::index-get name attachments)
          (assembly-checked-index-lines
           (cdr lines) defs names attachments sources packages entry target))
         (t
          (assembly-checked-index-lines
           (cdr lines) defs names
           (boymoo-compiler::index-set name (caddr line) attachments)
           (cons name sources) packages entry target))))
       ((and (or (equal word "package") (equal word "hidden-package"))
             (stringp name) (equal (char name 0) #\")
             (consp (cddr line)) (not (cdddr line))
             (or (equal (caddr line) boymoo-compiler::*nil-name*) (consp (caddr line))))
        (assembly-checked-index-lines
         (cdr lines) defs names attachments sources (cons line packages) entry target))
       ((and (equal word "entry") (not entry) (stringp name) (not (cddr line)))
        (assembly-checked-index-lines
         (cdr lines) defs names attachments sources packages name target))
       ((and (not target) (equal line '("target" "linux")))
        (assembly-checked-index-lines
         (cdr lines) defs names attachments sources packages entry :linux))
       (t (mv nil nil nil nil nil nil nil nil))))))

(defun assembly-checked-resolve-chain (name attachments resolved fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((cached (boymoo-compiler::index-get name resolved))
        (next (boymoo-compiler::index-get name attachments)))
    (cond ((equal cached :pending) (mv nil nil nil))
          (cached (mv t cached resolved))
          ((or (not next) (assoc-equal name boymoo-compiler::*primitives*)
               (equal name boymoo-compiler::*if-name*))
           (mv t name resolved))
          ((zp fuel) (mv nil nil nil))
          (t (mv-let (ok target resolved)
               (assembly-checked-resolve-chain
                next attachments (boymoo-compiler::index-set name :pending resolved) (1- fuel))
               (if ok
                   (mv t target (boymoo-compiler::index-set name target resolved))
                 (mv nil nil nil)))))))

(defun assembly-checked-resolve-attachments (sources attachments resolved fuel)
  (if (atom sources)
      (mv t resolved)
    (mv-let (ok target resolved)
      (assembly-checked-resolve-chain (car sources) attachments resolved fuel)
      (declare (ignore target))
      (if ok
          (assembly-checked-resolve-attachments (cdr sources) attachments resolved fuel)
        (mv nil nil)))))

(local (in-theory (disable boymoo-compiler::index-set boymoo-compiler::index-get
                           boymoo-compiler::declaration-list boymoo-compiler::symbol-separator
                           boymoo-compiler::reverse-onto assoc-equal char length
                           (:executable-counterpart boymoo-compiler::compiler-error))))

(defthm assembly-accepted-definition-index-agrees
  (mv-let (ok checked-defs checked-names)
    (assembly-checked-index-definitions items defs names seen)
    (implies ok
             (mv-let (actual-defs actual-names)
               (boymoo-compiler::index-definition-line items defs names seen)
               (and (equal actual-defs checked-defs)
                    (equal actual-names checked-names)))))
  :hints (("Goal" :induct (assembly-checked-index-definitions items defs names seen))))

(local (in-theory (disable assembly-checked-index-definitions
                           boymoo-compiler::index-definition-line)))

(defthm assembly-accepted-line-index-agrees
  (mv-let (ok defs-out names-out attachments-out sources-out packages-out entry-out target-out)
    (assembly-checked-index-lines lines defs names attachments sources packages entry target)
    (implies ok
             (mv-let (actual-defs actual-names actual-attachments actual-sources
                                  actual-packages actual-entry actual-target)
               (boymoo-compiler::index-lines lines defs names attachments sources packages entry target)
               (and (equal actual-defs defs-out)
                    (equal actual-names names-out)
                    (equal actual-attachments attachments-out)
                    (equal actual-sources sources-out)
                    (equal actual-packages packages-out)
                    (equal actual-entry entry-out)
                    (equal actual-target target-out)))))
  :hints (("Goal"
           :induct (assembly-checked-index-lines lines defs names attachments sources packages entry target))))

(defthm assembly-accepted-attachment-chain-agrees
  (mv-let (ok checked-target checked-resolved)
    (assembly-checked-resolve-chain name attachments resolved fuel)
    (implies ok
             (mv-let (actual-target actual-resolved)
               (boymoo-compiler::resolve-chain name attachments resolved fuel)
               (and (equal actual-target checked-target)
                    (equal actual-resolved checked-resolved)))))
  :hints (("Goal" :induct (assembly-checked-resolve-chain name attachments resolved fuel))))

(local (in-theory (disable assembly-checked-resolve-chain boymoo-compiler::resolve-chain)))

(defthm assembly-accepted-attachment-resolution-agrees
  (mv-let (ok checked)
    (assembly-checked-resolve-attachments sources attachments resolved fuel)
    (implies ok
             (equal (boymoo-compiler::resolve-attachments sources attachments resolved fuel)
                    checked)))
  :hints (("Goal" :induct (assembly-checked-resolve-attachments sources attachments resolved fuel))))

(defun assembly-checked-text-index (text)
  (mv-let (read-ok lines)
    (assembly-checked-read-program text)
    (if (not read-ok)
        (mv nil nil nil nil nil nil nil nil)
      (mv-let (index-ok defs names attachments sources packages entry target)
        (assembly-checked-index-lines lines nil nil nil nil nil nil nil)
        (if (not index-ok)
            (mv nil nil nil nil nil nil nil nil)
          (mv-let (resolution-ok resolved)
            (assembly-checked-resolve-attachments sources attachments nil (length sources))
            (mv resolution-ok lines defs names resolved packages entry target)))))))

(defthm assembly-accepted-text-index-agrees
  (mv-let (ok lines defs names resolved packages entry target)
    (assembly-checked-text-index text)
    (implies
     ok
     (let ((actual-lines (boymoo-compiler::read-program text)))
       (mv-let (actual-defs actual-names actual-attachments actual-sources
                            actual-packages actual-entry actual-target)
         (boymoo-compiler::index-lines actual-lines nil nil nil nil nil nil nil)
         (and (equal actual-lines lines)
              (equal actual-defs defs)
              (equal actual-names names)
              (equal actual-packages packages)
              (equal actual-entry entry)
              (equal actual-target target)
              (equal (boymoo-compiler::resolve-attachments
                      actual-sources actual-attachments nil (length actual-sources))
                     resolved))))))
  :hints (("Goal"
           :in-theory (disable assembly-checked-read-program boymoo-compiler::read-program
                               assembly-checked-index-lines boymoo-compiler::index-lines
                               assembly-checked-resolve-attachments boymoo-compiler::resolve-attachments))))
