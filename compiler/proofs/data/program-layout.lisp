(in-package "BOYMOO-PROOFS")

(include-book "allocation")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable data-state-sized-p data-block-sized-p mv-nth
                     boymoo-compiler::data-with-block boymoo-compiler::data-block
                     boymoo-compiler::data-list-cells boymoo-compiler::data-atom
                     boymoo-compiler::data-symbol boymoo-compiler::data-remember
                     boymoo-compiler::read-lines boymoo-compiler::index-get
                     boymoo-compiler::declaration-list boymoo-compiler::compiler-error
                     data-symbol-storage-input-p data-atom-storage-input-p char length)))

; Text that is decoded into a chunk must produce a string. Atoms and
; list items have different recursion boundaries at a dotted tail.
(defun data-datum-storage-input-p (kind parsed)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :datum) 1 0))))
  (cond ((eq kind :datum)
         (if (consp parsed)
             (data-datum-storage-input-p :items parsed)
           (data-atom-storage-input-p parsed)))
        ((atom parsed) t)
        ((equal (car parsed) ".") (data-atom-storage-input-p (cadr parsed)))
        (t (and (data-datum-storage-input-p :datum (car parsed))
                (data-datum-storage-input-p :items (cdr parsed))))))

(local
 (defthm datum-pass-preserves-sized-state
   (implies (and (data-datum-storage-input-p kind parsed) (data-state-sized-p state-data start)
                 (if (eq kind :datum) (equal reversed nil) (data-word-chunks-p reversed)))
            (let ((result (if (eq kind :datum)
                              (boymoo-compiler::data-datum parsed packages state-data)
                            (boymoo-compiler::data-list-datum parsed packages state-data reversed))))
              (and (not (stringp (mv-nth 0 result)))
                   (data-state-sized-p (mv-nth 1 result) start))))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-state-induction kind parsed packages state-data reversed))
           ("Subgoal *1/3"
            :use ((:instance data-list-cells-preserves-sized-block
                             (tail 34) (block (boymoo-compiler::data-block state-data)))
                  (:instance data-list-cells-preserves-sized-block
                             (tail (mv-nth 0 (boymoo-compiler::data-atom (cadr parsed) packages state-data)))
                             (block (boymoo-compiler::data-block
                                     (mv-nth 1 (boymoo-compiler::data-atom (cadr parsed) packages state-data)))))
                  (:instance data-atom-preserves-sized-state (text (cadr parsed))))
            :in-theory (disable data-list-cells-preserves-sized-block data-atom-preserves-sized-state)))))

(defthm data-datum-preserves-sized-state
  (implies (and (data-datum-storage-input-p :datum parsed) (data-state-sized-p state-data start))
           (and (not (stringp (mv-nth 0 (boymoo-compiler::data-datum parsed packages state-data))))
                (data-state-sized-p (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data)) start)))
  :hints (("Goal" :use ((:instance datum-pass-preserves-sized-state (kind :datum) (reversed nil)))
                  :in-theory (disable boymoo-compiler::data-datum data-datum-storage-input-p))))

(defun data-constant-storage-input-p (text)
  (if (equal (char text 0) #\()
      (data-datum-storage-input-p
       :datum (car (boymoo-compiler::read-lines text 0 (length text) nil nil nil (length text))))
    (data-atom-storage-input-p text)))

(local
 (in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum
                     data-datum-storage-input-p)))

(defthm data-constant-preserves-sized-state
  (implies (and (data-constant-storage-input-p text) (data-state-sized-p state-data start))
           (data-state-sized-p (boymoo-compiler::data-constant text packages state-data) start)))

(defthm data-note-symbol-preserves-sized-state
  (implies (and (data-symbol-storage-input-p text) (data-state-sized-p state-data start))
           (data-state-sized-p (boymoo-compiler::data-note-symbol text packages state-data) start)))

(defun data-formals-storage-input-p (formals)
  (if (atom formals)
      t
    (and (data-symbol-storage-input-p (car formals)) (data-formals-storage-input-p (cdr formals)))))

(local
 (in-theory (disable boymoo-compiler::data-note-symbol boymoo-compiler::data-constant
                     data-constant-storage-input-p)))

(defthm data-formals-preserve-sized-state
  (implies (and (data-formals-storage-input-p formals) (data-state-sized-p state-data start))
           (data-state-sized-p (boymoo-compiler::data-formals formals packages state-data) start))
  :hints (("Goal" :induct (boymoo-compiler::data-formals formals packages state-data))))

(defun data-term-storage-input-p (kind parsed depth)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (and (<= depth 10000)
           (cond ((atom parsed) (data-symbol-storage-input-p parsed))
                 ((equal (car parsed) boymoo-compiler::*quote-name*)
                  (and (stringp (cadr parsed)) (not (cddr parsed))
                       (data-constant-storage-input-p (cadr parsed))))
                 ((consp (car parsed))
                  (and (data-symbol-storage-input-p (caar parsed))
                       (data-formals-storage-input-p (boymoo-compiler::declaration-list (cadar parsed)))
                       (data-term-storage-input-p :term (caddar parsed) (1+ depth))
                       (data-term-storage-input-p :terms (cdr parsed) (1+ depth))))
                 (t (and (data-symbol-storage-input-p (car parsed))
                         (data-term-storage-input-p :terms (cdr parsed) (1+ depth))))))
    (or (atom parsed)
        (and (data-term-storage-input-p :term (car parsed) depth)
             (data-term-storage-input-p :terms (cdr parsed) depth)))))

(local (in-theory (disable boymoo-compiler::data-formals data-formals-storage-input-p)))

(local
 (defthm term-pass-preserves-sized-state
   (implies (and (data-state-sized-p state-data start) (data-term-storage-input-p kind parsed depth))
            (data-state-sized-p
             (if (eq kind :term) (boymoo-compiler::data-term parsed packages state-data depth)
               (boymoo-compiler::data-terms parsed packages state-data depth))
             start))
   :rule-classes nil
   :hints (("Goal" :induct (data-term-state-induction kind parsed packages state-data depth)))))

(defthm data-term-preserves-sized-state
  (implies (and (data-state-sized-p state-data start) (data-term-storage-input-p :term parsed depth))
           (data-state-sized-p (boymoo-compiler::data-term parsed packages state-data depth) start))
  :hints (("Goal" :use ((:instance term-pass-preserves-sized-state (kind :term)))
                  :in-theory (disable boymoo-compiler::data-term data-term-storage-input-p))))

(defun data-definitions-storage-input-p (items)
  (if (atom items)
      t
    (let ((definition (car items)))
      (and (data-symbol-storage-input-p (car definition))
           (data-formals-storage-input-p (boymoo-compiler::declaration-list (cadr definition)))
           (data-term-storage-input-p :term (caddr definition) 0)
           (data-definitions-storage-input-p (cdr items))))))

(local
 (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms data-term-storage-input-p)))

(defthm data-definitions-preserve-sized-state
  (implies (and (data-definitions-storage-input-p items) (data-state-sized-p state-data start))
           (data-state-sized-p (boymoo-compiler::data-definitions items packages state-data) start))
  :hints (("Goal" :induct (boymoo-compiler::data-definitions items packages state-data))))

(defun data-program-storage-input-p (lines)
  (if (atom lines)
      t
    (let* ((line (car lines))
           (word (car line)))
      (and (cond ((equal word "define")
                  (and (data-datum-storage-input-p :datum (cadr line))
                       (data-definitions-storage-input-p (cddr line))))
                 ((or (equal word "attach") (equal word "entry"))
                  (data-formals-storage-input-p (cdr line)))
                 ((equal word "heap-limit") nil)
                 (t t))
           (data-program-storage-input-p (cdr lines))))))

; The storage theorems describe the static block of a program without a
; heap limit, whose last allocation is the bucket vector.
(defthm data-storage-input-has-no-heap-limit
  (implies (data-program-storage-input-p lines)
           (not (boymoo-compiler::data-heap-limit lines nil)))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (boymoo-compiler::data-heap-limit lines nil)
                  :in-theory (enable boymoo-compiler::data-heap-limit))))

(defthm data-program-symbols-preserve-sized-state
  (implies (and (data-program-storage-input-p lines) (data-state-sized-p state-data start))
           (data-state-sized-p (boymoo-compiler::data-program-symbols lines packages state-data) start))
  :hints (("Goal" :induct (boymoo-compiler::data-program-symbols lines packages state-data)
                  :in-theory (disable boymoo-compiler::data-definitions data-definitions-storage-input-p))))
