(in-package "ACL2")

(include-book "structure-order")
(include-book "structure-events")

(local (in-theory (disable hons-acons hons-get structure-seen-index)))

; The initial signature and name inventories represent the primitives,
; definitions, named axioms and packages of the ground theory.

(defun structure-world-signatures (functions wrld)
  (if (endp functions)
      nil
    (cons (cons (car functions) (len (formals (car functions) wrld)))
          (structure-world-signatures (cdr functions) wrld))))

(defun structure-ground-signatures (ground-fns wrld)
  (structure-record-signatures
   (structure-world-signatures
    (append (strip-cars *primitive-formals-and-guards*) ground-fns) wrld)
   nil))

(defun structure-ground-names (ground-fns)
  (structure-record-names
   (append '(t nil)
           (strip-cars *primitive-formals-and-guards*)
           ground-fns
           *structure-ground-axioms*)
   nil))

(defun structure-ground-packages ()
  (structure-record-names *structure-ground-packages* nil))

(defun structure-ground-imports (packages known-packages table)
  (if (endp packages)
      table
    (let* ((package (car packages))
           (entry (find-package-entry package known-packages)))
      (structure-ground-imports
       (cdr packages) known-packages
       (structure-record-imports package (package-entry-imports entry) table)))))

(defun structure-ground-world-packages (wrld)
  (structure-ground-imports
   *structure-ground-packages*
   (getpropc 'known-package-alist 'global-value nil wrld)
   (structure-ground-packages)))

(defun structure-ground-contextp (ground-fns wrld signatures names packages)
  (and (equal signatures (structure-ground-signatures ground-fns wrld))
       (equal names (structure-ground-names ground-fns))
       (equal packages (structure-ground-world-packages wrld))))

(defthm structure-ground-arity-records
  (equal (structure-declared-signatures (bx-arities functions wrld))
         (structure-world-signatures functions wrld))
  :hints (("Goal" :in-theory (e/d (structure-declared-signatures) (formals)))))

(defthm structure-ground-axioms-agree
  (equal *bx-ground-axioms* *structure-ground-axioms*)
  :rule-classes nil)

(defthm structure-ground-imports-agree
  (equal (bx-add-package-imports packages known-packages table)
         (structure-ground-imports packages known-packages table))
  :hints (("Goal" :induct (structure-ground-imports packages known-packages table)
                  :in-theory (disable bx-add-imports structure-record-imports))))

(defthm structure-exporter-ground-context
  (implies (structure-ground-contextp ground-fns wrld signatures names packages)
           (equal (bx-ground-tables ground-fns wrld)
                  (list signatures names packages)))
  :hints (("Goal" :in-theory (disable bx-arities bx-add-arities bx-add-names
                                      bx-add-package-imports structure-ground-imports
                                      structure-world-signatures structure-record-imports
                                      structure-record-signatures structure-record-names)))
  :rule-classes nil)

; A book carries library failures as pairs of reason and data inside a
; single note.  Count its order failures as well as those for the book.

(defun structure-library-order-count (problems)
  (if (endp problems)
      0
    (+ (if (equal (caar problems) "line that could not be admitted in order") 1 0)
       (structure-library-order-count (cdr problems)))))

(defun structure-order-note-weight (reason data)
  (cond ((equal reason "line that could not be admitted in order") 1)
        ((equal reason "library whose lines could not be admitted in order")
         (structure-library-order-count data))
        (t 0)))

(defun structure-order-note-count (lines)
  (if (endp lines)
      0
    (+ (if (equal (caar lines) "note")
           (structure-order-note-weight (caadar lines) (cadadr (car lines)))
         0)
       (structure-order-note-count (cdr lines)))))

(defun structure-output-order-item-count (items)
  (if (endp items)
      0
    (+ (if (eq (caar items) :note)
           (structure-order-note-weight (cadar items) (caddar items))
         0)
       (structure-output-order-item-count (cdr items)))))

(defthm structure-output-order-count-of-append
  (equal (structure-output-order-item-count (append a b))
         (+ (structure-output-order-item-count a)
            (structure-output-order-item-count b))))

(defthm structure-output-order-count-includes-direct-notes
  (<= (structure-order-item-count items)
      (structure-output-order-item-count items))
  :rule-classes :linear)

(defthm structure-library-order-count-of-selected-items
  (equal (structure-library-order-count (bx-select :note items))
         (structure-order-item-count items)))

(defthm structure-order-count-of-wrapped-library
  (equal (structure-output-order-item-count (bx-library-problems items))
         (structure-order-item-count items))
  :hints (("Goal"
           :use ((:instance structure-library-order-count-of-selected-items))
           :in-theory (disable bx-select structure-library-order-count-of-selected-items))))

(defthm structure-order-note-count-of-append
  (equal (structure-order-note-count (append a b))
         (+ (structure-order-note-count a) (structure-order-note-count b))))

(defthm structure-order-notes-of-selected-items
  (equal (structure-order-note-count (bx-note-lines (bx-select :note items)))
         (structure-output-order-item-count items)))

(defthm structure-order-notes-of-count-lines
  (equal (structure-order-note-count (bx-count-lines lines)) 0)
  :hints (("Goal" :in-theory (disable bx-count-word))))

(defthm structure-order-count-of-book-notes
  (equal (structure-order-note-count
          (bx-note-lines (bx-book-notes items check-notes boot-hi lo hi books-dir cbd wrld)))
         (+ (structure-output-order-item-count items)
            (structure-output-order-item-count check-notes)))
  :hints (("Goal" :in-theory (disable bx-attachment-pairs bx-world-at
                                      bx-book-ttags global-val bx-skipped bx-events
                                      bx-marked-books
                                      structure-order-note-count))))

(defthm structure-order-failures-are-a-list
  (true-listp (car (structure-order-scan lines signatures names packages earlier)))
  :hints (("Goal" :induct (structure-order-scan lines signatures names packages earlier)
                  :in-theory (disable structure-line-orderp structure-signatures
                                      structure-names structure-record-signatures
                                      structure-record-names structure-record-package)))
  :rule-classes :type-prescription)

(defthm structure-length-of-empty-true-list
  (implies (true-listp xs)
           (equal (equal (len xs) 0) (not xs)))
  :hints (("Goal" :cases ((consp xs)) :in-theory (enable len))))

(defthm structure-order-failures-have-zero-length
  (equal (equal (len (car (structure-order-scan lines signatures names packages earlier))) 0)
         (not (car (structure-order-scan lines signatures names packages earlier))))
  :hints (("Goal" :in-theory (disable structure-order-scan))))

(defthm structure-first-audit-count
  (equal (structure-order-item-count
          (car (bx-check-stmts lines signatures names packages nil nil)))
         (len (car (structure-order-scan lines signatures names packages nil))))
  :hints (("Goal" :use ((:instance structure-check-statements-order
                                   (earlier nil) (notes nil)))
                  :in-theory (disable bx-check-stmts structure-order-scan
                                      structure-seen-index structure-order-item-count))))

(defthm structure-book-audit-count
  (let* ((prefix (bx-check-stmts library signatures names packages nil nil))
         (checked (bx-check-stmts lines (mv-nth 1 prefix) (mv-nth 2 prefix)
                                (mv-nth 3 prefix) (mv-nth 4 prefix) nil))
         (model-prefix (structure-order-scan library signatures names packages nil))
         (model-book (structure-order-scan
                      lines (mv-nth 1 model-prefix) (mv-nth 2 model-prefix)
                      (mv-nth 3 model-prefix) (mv-nth 4 model-prefix))))
    (equal (structure-order-item-count (car checked))
           (len (car model-book))))
  :hints (("Goal"
           :use ((:instance structure-check-statements-order
                            (lines library) (earlier nil) (notes nil))
                 (:instance structure-check-statements-order
                            (signatures (mv-nth 1 (structure-order-scan
                                                   library signatures names packages nil)))
                            (names (mv-nth 2 (structure-order-scan
                                              library signatures names packages nil)))
                            (packages (mv-nth 3 (structure-order-scan
                                                 library signatures names packages nil)))
                            (earlier (mv-nth 4 (structure-order-scan
                                                library signatures names packages nil)))
                            (notes nil)))
           :in-theory (disable bx-check-stmts structure-order-scan structure-order-item-count
                               structure-seen-index))))

; The statement data have the prefix order of spec/formats.md when
; interpreted in its canonical format.

(local (in-theory (disable bx-library-lines bx-book-lines bx-items bx-events bx-enclose
                           bx-library-order bx-ground-tables bx-count-lines bx-not-ground
                           bx-check-stmts bx-book-notes bx-range-items bx-select bx-note-lines
                           bx-runnable bx-library-program-order bx-attach-lines
                           bx-attachment-pairs bx-ground-defines bx-event-aids bx-world-at
                           structure-ground-contextp structure-order-scan
                           structure-order-scan-of-append bx-library-problems
                           structure-order-note-count structure-order-item-count
                           structure-output-order-item-count)))

(defthm structure-library-notes-count-order-failures
  (implies (structure-ground-contextp ground-fns wrld signatures names packages)
           (let* ((result (bx-library-lines ground-fns hi translations wrld))
                  (expected (structure-order-scan
                             (car result) signatures names packages nil)))
             (<= (len (car expected))
                 (structure-order-note-count (mv-nth 2 result)))))
  :hints (("Goal" :expand ((bx-library-lines ground-fns hi translations wrld))
                  :use ((:instance structure-exporter-ground-context)))))

(defthm structure-library-lines-order-or-note
  (let* ((result (bx-library-lines ground-fns hi translations wrld))
         (lines (car result)))
    (implies (structure-ground-contextp ground-fns wrld signatures names packages)
             (or (structure-orderp lines signatures names packages)
                 (< 0 (structure-order-note-count (mv-nth 2 result))))))
  :hints (("Goal" :use ((:instance structure-library-notes-count-order-failures))
                  :in-theory (disable structure-order-failures-have-zero-length))))

; The book reruns the library pass in the book world.  LIBRARY is the
; actual preceding input to which the result is to be appended.

(defun structure-library-prefix-matches-p (library ground-fns boot-hi wrld)
  (mv-let (statements program notes)
    (bx-library-lines ground-fns boot-hi nil wrld)
    (declare (ignore program notes))
    (equal library statements)))

(defthm structure-matching-library-statements
  (implies (structure-library-prefix-matches-p library ground-fns boot-hi wrld)
           (equal
            (car (bx-library-order
                  (bx-not-ground
                   (bx-select :stmt
                              (bx-items
                               (bx-enclose (reverse (bx-events wrld 0 boot-hi nil)) nil nil wrld)
                               nil nil nil wrld nil))
                   ground-fns)))
            library))
  :hints (("Goal" :expand ((bx-library-lines ground-fns boot-hi nil wrld))))
  :rule-classes nil)

(local (defthm structure-length-of-append
         (equal (len (append a b)) (+ (len a) (len b)))))

(defthm structure-order-failure-count-of-append
  (let* ((prefix (structure-order-scan library signatures names packages nil))
         (extension (structure-order-scan
                     lines (mv-nth 1 prefix) (mv-nth 2 prefix)
                     (mv-nth 3 prefix) (mv-nth 4 prefix))))
    (equal (len (car (structure-order-scan
                      (append library lines) signatures names packages nil)))
           (+ (len (car prefix)) (len (car extension)))))
  :hints (("Goal" :in-theory (enable structure-order-scan-of-append))))

(defthm structure-book-notes-count-order-failures
  (implies
   (and (structure-ground-contextp ground-fns wrld signatures names packages)
        (structure-library-prefix-matches-p library ground-fns boot-hi wrld))
   (let* ((result (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
          (expected (structure-order-scan
                     (append library (car result)) signatures names packages nil)))
     (<= (len (car expected))
         (structure-order-note-count (mv-nth 2 result)))))
  :hints (("Goal"
           :expand ((bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
           :use ((:instance structure-matching-library-statements)
                 (:instance structure-exporter-ground-context))
           :in-theory (disable structure-library-prefix-matches-p))))

(defthm structure-book-lines-order-or-note
  (let* ((result (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
         (lines (append library (car result))))
    (implies (and (structure-ground-contextp ground-fns wrld signatures names packages)
                  (structure-library-prefix-matches-p library ground-fns boot-hi wrld))
             (or (structure-orderp lines signatures names packages)
                 (< 0 (structure-order-note-count (mv-nth 2 result))))))
  :hints (("Goal"
           :use ((:instance structure-book-notes-count-order-failures))
           :in-theory (e/d (structure-order-scan-of-append)
                           (structure-library-prefix-matches-p
                            structure-order-failures-have-zero-length)))))
