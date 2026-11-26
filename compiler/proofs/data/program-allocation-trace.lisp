(in-package "BOYMOO-PROOFS")

(include-book "value-allocation-trace")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::data-block boymoo-compiler::data-symbol boymoo-compiler::data-constant
                     boymoo-compiler::data-datum boymoo-compiler::declaration-list
                     data-state-sized-p data-symbol-storage-input-p data-datum-storage-input-p
                     data-constant-storage-input-p data-allocation-trace-block
                     data-symbol-allocation-trace data-constant-allocation-trace data-datum-allocation-trace)))

(local
 (defthm append-allocation-traces-associates
   (equal (append (append first second) rest) (append first second rest))))

(local
 (defthm sized-compiler-state-has-a-sized-block
   (implies (data-state-sized-p state-data 80)
            (and (consp (boymoo-compiler::data-block state-data))
                 (integerp (car (boymoo-compiler::data-block state-data)))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-state-sized-p data-block-sized-p)))))

(defthmd data-note-symbol-allocation-trace-is-the-symbol-block
  (implies (and (data-state-sized-p state-data 80) (data-symbol-storage-input-p text))
           (equal (boymoo-compiler::data-block (boymoo-compiler::data-note-symbol text packages state-data))
                  (data-allocation-trace-block (data-symbol-allocation-trace text packages state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :in-theory (enable data-symbol-allocation-trace-is-the-symbol-block))))

(local (in-theory (disable boymoo-compiler::data-note-symbol)))

(defun data-formals-allocation-trace (formals packages state-data)
  (if (atom formals)
      nil
    (append (data-symbol-allocation-trace (car formals) packages state-data)
            (data-formals-allocation-trace (cdr formals) packages
                                          (boymoo-compiler::data-note-symbol (car formals) packages state-data)))))

(defthmd data-formals-allocation-trace-is-the-formals-block
  (implies (and (data-state-sized-p state-data 80) (data-formals-storage-input-p formals))
           (equal (boymoo-compiler::data-block (boymoo-compiler::data-formals formals packages state-data))
                  (data-allocation-trace-block (data-formals-allocation-trace formals packages state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :induct (data-formals-allocation-trace formals packages state-data)
                  :in-theory (enable data-note-symbol-allocation-trace-is-the-symbol-block
                                     data-following-allocation-traces-appends-their-objects))))

(local
 (in-theory (disable boymoo-compiler::data-formals data-formals-allocation-trace data-formals-storage-input-p)))

(defun data-term-allocation-trace (kind parsed packages state-data depth)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (cond ((< 10000 depth) nil)
            ((atom parsed) (data-symbol-allocation-trace parsed packages state-data))
            ((equal (car parsed) boymoo-compiler::*quote-name*)
             (if (and (stringp (cadr parsed)) (not (cddr parsed)))
                 (append (data-symbol-allocation-trace boymoo-compiler::*quote-name* packages state-data)
                         (data-constant-allocation-trace
                          (cadr parsed) packages (boymoo-compiler::data-note-symbol
                                                  boymoo-compiler::*quote-name* packages state-data)))
               nil))
            ((consp (car parsed))
             (let* ((head (car parsed)) (formals (boymoo-compiler::declaration-list (cadr head)))
                    (named (boymoo-compiler::data-note-symbol (car head) packages state-data))
                    (bound (boymoo-compiler::data-formals formals packages named))
                    (body (boymoo-compiler::data-term (caddr head) packages bound (1+ depth))))
               (append (data-symbol-allocation-trace (car head) packages state-data)
                       (data-formals-allocation-trace formals packages named)
                       (data-term-allocation-trace :term (caddr head) packages bound (1+ depth))
                       (data-term-allocation-trace :terms (cdr parsed) packages body (1+ depth)))))
            (t (append (data-symbol-allocation-trace (car parsed) packages state-data)
                       (data-term-allocation-trace :terms (cdr parsed) packages
                                                   (boymoo-compiler::data-note-symbol
                                                    (car parsed) packages state-data) (1+ depth)))))
    (if (atom parsed)
        nil
      (append (data-term-allocation-trace :term (car parsed) packages state-data depth)
              (data-term-allocation-trace :terms (cdr parsed) packages
                                          (boymoo-compiler::data-term (car parsed) packages state-data depth) depth)))))

(defthmd data-term-allocation-trace-is-the-term-block
  (implies (and (data-state-sized-p state-data 80) (data-term-storage-input-p kind parsed depth))
           (equal (boymoo-compiler::data-block
                   (if (eq kind :term) (boymoo-compiler::data-term parsed packages state-data depth)
                     (boymoo-compiler::data-terms parsed packages state-data depth)))
                  (data-allocation-trace-block (data-term-allocation-trace kind parsed packages state-data depth)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :induct (data-term-allocation-trace kind parsed packages state-data depth)
                  :in-theory (e/d (data-note-symbol-allocation-trace-is-the-symbol-block
                                   data-formals-allocation-trace-is-the-formals-block
                                   data-constant-allocation-trace-is-the-constant-block
                                   data-following-allocation-traces-appends-their-objects)
                                  (boymoo-compiler::data-term boymoo-compiler::data-terms data-term-storage-input-p))
                  :expand ((boymoo-compiler::data-term parsed packages state-data depth)
                           (boymoo-compiler::data-terms parsed packages state-data depth)
                           (:free (mode) (data-term-storage-input-p mode parsed depth))))))

(local
 (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms data-term-allocation-trace
                     data-term-storage-input-p)))

(local
 (defthm term-trace-equals-the-block-after-one-term
   (implies (and (data-state-sized-p state-data 80) (data-term-storage-input-p :term parsed depth))
            (equal (boymoo-compiler::data-block (boymoo-compiler::data-term parsed packages state-data depth))
                   (data-allocation-trace-block (data-term-allocation-trace :term parsed packages state-data depth)
                                                (boymoo-compiler::data-block state-data))))
   :hints (("Goal" :use ((:instance data-term-allocation-trace-is-the-term-block (kind :term)))))))

(defun data-definitions-allocation-trace (definitions packages state-data)
  (if (atom definitions)
      nil
    (let* ((definition (car definitions)) (name (car definition))
           (formals (boymoo-compiler::declaration-list (cadr definition))) (body (caddr definition))
           (named (boymoo-compiler::data-note-symbol name packages state-data))
           (bound (boymoo-compiler::data-formals formals packages named))
           (next (boymoo-compiler::data-term body packages bound 0)))
      (append (data-symbol-allocation-trace name packages state-data)
              (data-formals-allocation-trace formals packages named)
              (data-term-allocation-trace :term body packages bound 0)
              (data-definitions-allocation-trace (cdr definitions) packages next)))))

(defthmd data-definitions-allocation-trace-is-the-definition-block
  (implies (and (data-state-sized-p state-data 80) (data-definitions-storage-input-p definitions))
           (equal (boymoo-compiler::data-block (boymoo-compiler::data-definitions definitions packages state-data))
                  (data-allocation-trace-block (data-definitions-allocation-trace definitions packages state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :induct (data-definitions-allocation-trace definitions packages state-data)
                  :in-theory (enable data-note-symbol-allocation-trace-is-the-symbol-block
                                     data-formals-allocation-trace-is-the-formals-block
                                     data-following-allocation-traces-appends-their-objects))))

(local
 (in-theory (disable boymoo-compiler::data-definitions data-definitions-allocation-trace
                     data-definitions-storage-input-p)))

(defun data-program-allocation-trace (lines packages state-data)
  (if (atom lines)
      nil
    (let* ((line (car lines)) (word (car line)))
      (cond ((equal word "define")
             (mv-let (rulers next) (boymoo-compiler::data-datum (cadr line) packages state-data)
               (declare (ignore rulers))
               (append (data-datum-allocation-trace :datum (cadr line) packages state-data nil)
                       (data-definitions-allocation-trace (cddr line) packages next)
                       (data-program-allocation-trace
                        (cdr lines) packages (boymoo-compiler::data-definitions (cddr line) packages next)))))
            ((or (equal word "attach") (equal word "entry"))
             (append (data-formals-allocation-trace (cdr line) packages state-data)
                     (data-program-allocation-trace
                      (cdr lines) packages (boymoo-compiler::data-formals (cdr line) packages state-data))))
            (t (data-program-allocation-trace (cdr lines) packages state-data))))))

(defthmd data-program-allocation-trace-is-the-program-block
  (implies (and (data-state-sized-p state-data 80) (data-program-storage-input-p lines))
           (equal (boymoo-compiler::data-block (boymoo-compiler::data-program-symbols lines packages state-data))
                  (data-allocation-trace-block (data-program-allocation-trace lines packages state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :induct (data-program-allocation-trace lines packages state-data)
                  :in-theory (enable data-datum-allocation-trace-is-the-datum-block
                                     data-formals-allocation-trace-is-the-formals-block
                                     data-definitions-allocation-trace-is-the-definition-block
                                     data-following-allocation-traces-appends-their-objects))))
