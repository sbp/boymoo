(in-package "BOYMOO-PROOFS")

(include-book "static-symbols")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable length char ash
                           boymoo-compiler::hex-byte boymoo-compiler::index-get
                           boymoo-compiler::symbol-separator boymoo-compiler::decode-part
                           boymoo-compiler::read-lines boymoo-compiler::data-remember
                           boymoo-compiler::data-with-block boymoo-compiler::data-text
                           boymoo-compiler::data-block
                           boymoo-compiler::data-number boymoo-compiler::data-symbol
                           boymoo-compiler::data-note-symbol boymoo-compiler::data-formals
                           boymoo-compiler::data-list-cells
                           (:executable-counterpart boymoo-compiler::compiler-error)
                           assembly-static-block-p assembly-static-datum-word-p
                           assembly-static-data-state-p assembly-static-symbol-input-p
                           assembly-static-number-input-p)))

(local
 (defthm assembly-first-static-term-result
   (equal (mv-nth 0 values) (car values))))

(local
 (defthm assembly-second-static-term-result
   (equal (mv-nth 1 values) (cadr values))))

(defun assembly-static-atom-input-p (text)
  (let ((first (char text 0)))
    (and (stringp text)
         (case first
           (#\" (stringp (boymoo-compiler::decode-part text 0 (length text))))
           (otherwise
            (cond ((and (not (equal first #\#)) (boymoo-compiler::symbol-separator text))
                   (assembly-static-symbol-input-p text))
                  ((and (equal first #\#) (equal (char text 1) #\\)
                        (equal (length text) 4))
                   t)
                  (t (assembly-static-number-input-p text))))))))

(local
 (defthm assembly-constant-lookup-is-static-word
   (implies (assembly-static-data-state-p state-data)
            (assembly-static-datum-word-p
             (boymoo-compiler::index-get text (cadr state-data))))
   :hints (("Goal" :in-theory (enable assembly-static-data-state-p)))))

(defthm assembly-static-state-collects-atom
  (let ((out (boymoo-compiler::data-atom text packages state-data)))
    (implies (and (assembly-static-data-state-p state-data) (assembly-static-atom-input-p text))
             (and (assembly-static-datum-word-p (car out))
                  (assembly-static-data-state-p (cadr out))))))

(mutual-recursion
 (defun assembly-static-datum-input-p (datum)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count datum)))))
   (if (consp datum)
       (assembly-static-list-input-p datum)
     (assembly-static-atom-input-p datum)))
 (defun assembly-static-list-input-p (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (cond ((atom items) t)
         ((equal (car items) ".")
          (and (consp (cdr items)) (not (cddr items))
               (assembly-static-atom-input-p (cadr items))))
         (t (and (assembly-static-datum-input-p (car items))
                 (assembly-static-list-input-p (cdr items)))))))

(local (in-theory (disable boymoo-compiler::data-atom assembly-static-atom-input-p)))

(set-irrelevant-formals-ok t)

(local
 (defun assembly-collect-datum-induction (datum-p item packages state-data reversed)
   (declare (xargs :measure (+ (* 2 (acl2-count item)) (if datum-p 1 0))))
   (cond (datum-p
          (and (consp item)
               (assembly-collect-datum-induction nil item packages state-data nil)))
         ((or (atom item) (equal (car item) ".")) nil)
         (t
          (mv-let (datum next)
            (boymoo-compiler::data-datum (car item) packages state-data)
            (list (assembly-collect-datum-induction t (car item) packages state-data nil)
                  (assembly-collect-datum-induction nil (cdr item) packages next
                                                     (cons datum reversed))))))))

(local
 (defthm assembly-datum-collection-invariant
   (let ((out (if datum-p
                  (boymoo-compiler::data-datum item packages state-data)
                (boymoo-compiler::data-list-datum item packages state-data reversed))))
     (implies (and (assembly-static-data-state-p state-data)
                   (if datum-p
                       (assembly-static-datum-input-p item)
                     (and (assembly-static-list-input-p item)
                          (assembly-static-words-p reversed))))
              (and (assembly-static-datum-word-p (car out))
                   (assembly-static-data-state-p (cadr out)))))
   :hints (("Goal" :induct (assembly-collect-datum-induction datum-p item packages state-data reversed)))
   :rule-classes nil))

(defthm assembly-static-state-collects-datum
  (let ((out (boymoo-compiler::data-datum datum packages state-data)))
    (implies (and (assembly-static-data-state-p state-data) (assembly-static-datum-input-p datum))
             (and (assembly-static-datum-word-p (car out))
                  (assembly-static-data-state-p (cadr out)))))
  :hints (("Goal"
           :use ((:instance assembly-datum-collection-invariant
                            (datum-p t) (item datum) (reversed nil)))
           :in-theory (disable boymoo-compiler::data-datum
                               boymoo-compiler::data-list-datum assembly-static-datum-input-p))))

(defun assembly-static-constant-input-p (text)
  (if (equal (char text 0) #\()
      (assembly-static-datum-input-p
       (car (boymoo-compiler::read-lines text 0 (length text) nil nil nil (length text))))
    (assembly-static-atom-input-p text)))

(local (in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum
                           assembly-static-datum-input-p assembly-static-list-input-p)))

(defthm assembly-static-state-collects-constant
  (implies (and (assembly-static-data-state-p state-data) (assembly-static-constant-input-p text))
           (assembly-static-data-state-p (boymoo-compiler::data-constant text packages state-data))))

(local (in-theory (disable boymoo-compiler::data-constant assembly-static-constant-input-p
                           boymoo-compiler::declaration-list)))

(mutual-recursion
 (defun assembly-static-term-input-p (term depth)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (and (<= depth 10000)
        (cond ((atom term) (assembly-static-symbol-input-p term))
              ((equal (car term) boymoo-compiler::*quote-name*)
               (and (stringp (cadr term)) (not (cddr term))
                    (assembly-static-constant-input-p (cadr term))))
              ((consp (car term))
               (and (assembly-static-symbol-input-p (caar term))
                    (assembly-static-symbol-list-p
                     (boymoo-compiler::declaration-list (cadar term)))
                    (assembly-static-term-input-p (caddar term) (+ depth 1))
                    (assembly-static-terms-input-p (cdr term) (+ depth 1))))
              (t (and (assembly-static-symbol-input-p (car term))
                      (assembly-static-terms-input-p (cdr term) (+ depth 1)))))))
 (defun assembly-static-terms-input-p (terms depth)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (or (atom terms)
       (and (assembly-static-term-input-p (car terms) depth)
            (assembly-static-terms-input-p (cdr terms) depth)))))

(local
 (defun assembly-collect-terms-induction (term-p text packages state-data depth)
   (declare (xargs :measure (+ (* 2 (acl2-count text)) (if term-p 1 0))))
   (if term-p
       (cond ((or (< 10000 depth) (atom text)
                  (equal (car text) boymoo-compiler::*quote-name*)) nil)
             ((consp (car text))
              (let* ((head (car text))
                     (named (boymoo-compiler::data-note-symbol (car head) packages state-data))
                     (scoped (boymoo-compiler::data-formals
                              (boymoo-compiler::declaration-list (cadr head)) packages named)))
                (list (assembly-collect-terms-induction t (caddr head) packages scoped (+ depth 1))
                      (assembly-collect-terms-induction
                       nil (cdr text) packages
                       (boymoo-compiler::data-term (caddr head) packages scoped (+ depth 1))
                       (+ depth 1)))))
             (t (assembly-collect-terms-induction
                 nil (cdr text) packages
                 (boymoo-compiler::data-note-symbol (car text) packages state-data)
                 (+ depth 1))))
     (and (consp text)
          (list (assembly-collect-terms-induction t (car text) packages state-data depth)
                (assembly-collect-terms-induction
                 nil (cdr text) packages (boymoo-compiler::data-term (car text) packages state-data depth)
                 depth))))))

(local
 (defthm assembly-term-collection-invariant
   (implies (and (assembly-static-data-state-p state-data)
                 (if term-p
                     (assembly-static-term-input-p text depth)
                   (assembly-static-terms-input-p text depth)))
            (assembly-static-data-state-p
             (if term-p
                 (boymoo-compiler::data-term text packages state-data depth)
               (boymoo-compiler::data-terms text packages state-data depth))))
   :hints (("Goal" :induct (assembly-collect-terms-induction term-p text packages state-data depth)))
   :rule-classes nil))

(set-irrelevant-formals-ok nil)

(defthm assembly-static-state-collects-term
  (implies (and (assembly-static-data-state-p state-data) (assembly-static-term-input-p text depth))
           (assembly-static-data-state-p
            (boymoo-compiler::data-term text packages state-data depth)))
  :hints (("Goal" :use ((:instance assembly-term-collection-invariant (term-p t)))
                  :in-theory (disable boymoo-compiler::data-term assembly-static-term-input-p))))

(local (in-theory (disable boymoo-compiler::data-term assembly-static-term-input-p)))

(defun assembly-static-definitions-input-p (definitions)
  (if (atom definitions)
      t
    (let ((definition (car definitions)))
      (and (assembly-static-symbol-input-p (car definition))
           (assembly-static-symbol-list-p (boymoo-compiler::declaration-list (cadr definition)))
           (assembly-static-term-input-p (caddr definition) 0)
           (assembly-static-definitions-input-p (cdr definitions))))))

(local
 (defthm assembly-static-state-collects-definitions
   (implies (and (assembly-static-data-state-p state-data)
                 (assembly-static-definitions-input-p definitions))
            (assembly-static-data-state-p
             (boymoo-compiler::data-definitions definitions packages state-data)))
   :hints (("Goal" :induct (boymoo-compiler::data-definitions definitions packages state-data)))))

(defun assembly-static-program-input-p (lines)
  (if (atom lines)
      t
    (let ((line (car lines)))
      (and (cond ((equal (car line) "define")
                 (and (assembly-static-datum-input-p (cadr line))
                      (assembly-static-definitions-input-p (cddr line))))
                ((member-equal (car line) '("attach" "entry"))
                 (assembly-static-symbol-list-p (cdr line)))
                (t t))
           (assembly-static-program-input-p (cdr lines))))))

(defthm assembly-static-state-collects-program
  (implies (and (assembly-static-data-state-p state-data) (assembly-static-program-input-p lines))
           (assembly-static-data-state-p
            (boymoo-compiler::data-program-symbols lines packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-program-symbols lines packages state-data)
                  :in-theory (disable boymoo-compiler::data-definitions
                                      assembly-static-definitions-input-p
                                      assembly-static-symbol-list-p))))
