(in-package "ACL2")

(include-book "structure-coverage")
(include-book "structure-ground-filter")
(include-book "structure-entry-order")
(include-book "structure-counts")

(local (in-theory (disable hons-acons hons-get structure-seen-index)))

; The range hypotheses concern the stored event numbers and depths.
; Interpret the range independently, including the landmark at HI.

(defun structure-range-pairs (wrld lo hi)
  (structure-pair-range-events
   (reverse (structure-range-events wrld lo hi nil))
   nil wrld nil))

(defun structure-range-recordsp (wrld lo hi)
  (and (structure-decreasing-landmarks-p wrld nil)
       (structure-event-depths-are-integers-p
        (structure-range-events wrld lo hi nil))))

(defun structure-range-namep (name record lo hi wrld)
  (and (structure-event-in-rangep record lo hi wrld)
       (member-equal name (structure-event-names record))))

(defthm structure-range-pairs-agree
  (implies (structure-range-recordsp wrld lo hi)
           (equal (bx-enclose (reverse (bx-events wrld lo hi nil)) nil nil wrld)
                  (structure-range-pairs wrld lo hi)))
  :hints (("Goal"
           :use ((:instance structure-events-implementation (upper nil) (acc nil))
                 (:instance structure-enclose-implements-pairing
                            (newest (reverse (structure-range-events wrld lo hi nil)))
                            (later nil) (acc nil)))
           :in-theory (disable bx-events bx-enclose structure-range-events
                               structure-pair-range-events
                               structure-enclose-implements-pairing))))

(defthm structure-records-in-pairs
  (equal (strip-cars (structure-pair-range-events newest later wrld acc))
         (revappend newest (strip-cars acc)))
  :hints (("Goal" :induct (structure-pair-range-events newest later wrld acc)
                  :in-theory (disable structure-nearest-root structure-enclosing-landmarks))))

(defthm structure-revappend-of-revappend
  (equal (revappend (revappend a b) c)
         (revappend b (append a c)))
  :hints (("Goal" :induct (revappend a b))))

(defthm structure-range-forms-a-true-list
  (implies (true-listp acc)
           (true-listp (structure-range-events wrld lo hi acc)))
  :hints (("Goal" :induct (structure-range-events wrld lo hi acc)
                  :in-theory (disable structure-event-number)))
  :rule-classes :type-prescription)

(defthm structure-records-of-range-pairs
  (equal (strip-cars (structure-range-pairs wrld lo hi))
         (structure-range-events wrld lo hi nil))
  :hints (("Goal" :in-theory (disable structure-pair-range-events structure-range-events))))

(defthm structure-range-pairs-are-closed
  (structure-closed-pairs-p (structure-range-pairs wrld lo hi) wrld)
  :hints (("Goal" :use ((:instance structure-pairing-keeps-carriers
                                   (newest (reverse (structure-range-events wrld lo hi nil)))
                                   (later nil) (acc nil)))
                  :in-theory (disable structure-pairing-keeps-carriers
                                      structure-pair-range-events structure-range-events))))

(defthm structure-empty-name-table
  (not (hons-get name nil))
  :hints (("Goal" :in-theory (enable hons-get))))

(defthm structure-raw-range-accounts-for-name
  (implies
   (and (structure-range-recordsp wrld lo hi)
        (structure-range-namep name record lo hi wrld)
        (structure-namex-shapep record)
        (not (structure-no-statement-due-p name record wrld)))
   (structure-items-account-for-p name (bx-range-items lo hi translations wrld)))
  :hints (("Goal"
           :use ((:instance structure-items-cover-range-name
                            (pairs (structure-range-pairs wrld lo hi))
                            (pending nil) (defined nil) (acc nil))
                 (:instance structure-range-pairs-agree))
           :in-theory (disable bx-events bx-enclose bx-items reverse
                               structure-range-pairs-agree structure-coverage-is-statement-or-note
                               structure-items-cover-range-name
                               structure-range-pairs structure-event-names
                               structure-range-recordsp structure-namex-shapep
                               structure-no-statement-due-p
                               structure-range-events structure-event-in-rangep
                               structure-items-account-for-p))))

; Coverage notes and order notes are retained when selecting, formatting
; and adjoining the counts.  An order note can name the second use of a
; symbol even if some unrelated line also fails.

(defthm structure-select-of-append
  (equal (bx-select key (append a b))
         (append (bx-select key a) (bx-select key b))))

(defthm structure-note-lines-of-append
  (equal (bx-note-lines (append a b))
         (append (bx-note-lines a) (bx-note-lines b))))

(defthm structure-coverage-notes-of-append
  (iff (structure-notes-report-p name (append a b))
       (or (structure-notes-report-p name a)
           (structure-notes-report-p name b))))

(defthm structure-book-notes-retain-coverage
  (implies (structure-notes-report-p name (bx-note-lines (bx-select :note items)))
           (structure-notes-report-p name
                                     (bx-note-lines (bx-book-notes
                                                     items check-notes boot-hi lo hi
                                                     books-dir cbd wrld))))
  :hints (("Goal" :in-theory (disable bx-attachment-pairs bx-world-at bx-book-ttags
                                      global-val bx-skipped bx-events bx-marked-books
                                      bx-select bx-note-lines))))

(defthm structure-book-notes-retain-conflicts
  (implies (structure-order-notes-report-conflict-p name
                                                    (bx-note-lines (bx-select :note check-notes)))
           (structure-order-notes-report-conflict-p
            name (bx-note-lines (bx-book-notes items check-notes boot-hi lo hi books-dir cbd wrld))))
  :hints (("Goal" :in-theory (disable bx-attachment-pairs bx-world-at bx-book-ttags
                                      global-val bx-skipped bx-events bx-marked-books
                                      bx-select bx-note-lines))))

(defun structure-name-has-note-p (name notes)
  (or (structure-notes-report-p name notes)
      (structure-order-notes-report-conflict-p name notes)))

; The library omits statements for names supplied by the ground theory.
; It retains the statements it orders and the notes that account for
; names without statements.

(defthm structure-empty-input-supplies-no-name
  (not (structure-lines-supply-p name nil)))

(local (in-theory (disable bx-library-lines bx-book-lines bx-range-items bx-items
                           bx-events bx-enclose bx-library-order bx-ground-tables
                           bx-check-stmts bx-count-lines bx-select bx-note-lines
                           bx-book-notes bx-not-ground bx-runnable bx-library-program-order
                           bx-attach-lines bx-attachment-pairs bx-ground-defines
                           bx-event-aids bx-world-at reverse structure-lines-supply-p
                           structure-event-lines-supply-p structure-range-pairs
                           structure-items-account-for-p structure-range-recordsp
                           structure-range-namep
                           structure-namex-shapep structure-no-statement-due-p
                           structure-library-ground-supplies-p structure-notes-report-p
                           structure-order-notes-report-conflict-p
                           structure-order-items-report-conflict-p
                           structure-introduction-count structure-order-scan
                           structure-order-scan-of-append structure-library-prefix-matches-p)))

(defthm structure-library-lines-supply-or-note
  (implies
   (and (structure-range-recordsp wrld 0 hi)
        (structure-range-namep name record 0 hi wrld)
        (structure-namex-shapep record)
        (not (structure-no-statement-due-p name record wrld))
        (not (structure-library-ground-supplies-p name ground-fns)))
   (let ((result (bx-library-lines ground-fns hi translations wrld)))
     (or (structure-lines-supply-p name (car result))
         (structure-notes-report-p name (mv-nth 2 result)))))
  :hints (("Goal"
           :expand ((bx-library-lines ground-fns hi translations wrld))
           :use ((:instance structure-raw-range-accounts-for-name (lo 0))
                 (:instance structure-library-filter-keeps-name
                            (lines (bx-select :stmt (bx-range-items 0 hi translations wrld)))))
           :in-theory (e/d (bx-range-items)
                           (structure-raw-range-accounts-for-name structure-library-filter-keeps-name)))))

(defthm structure-book-lines-supply-or-note
  (implies
   (and (structure-range-recordsp wrld lo hi)
        (structure-range-namep name record lo hi wrld)
        (structure-namex-shapep record)
        (not (structure-no-statement-due-p name record wrld)))
   (let ((result (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld)))
     (or (structure-lines-supply-p name (car result))
         (structure-notes-report-p name (mv-nth 2 result)))))
  :hints (("Goal"
           :expand ((bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
           :use ((:instance structure-raw-range-accounts-for-name))
           :in-theory (disable structure-raw-range-accounts-for-name))))

; A distinct second statement for the same symbol is diagnosed.  An
; identical line is tested only at its first occurrence.

(defthm structure-first-audit-reports-second-introduction
  (implies (< 1 (structure-introduction-count name lines nil))
           (structure-order-items-report-conflict-p
            name (car (bx-check-stmts lines signatures names packages nil nil))))
  :hints (("Goal"
           :use ((:instance structure-audit-reports-repeat-of-name
                            (earlier nil) (notes nil))
                 (:instance structure-package-introduced-at-most-once (earlier nil)))
           :in-theory (disable structure-audit-reports-repeat-of-name
                               (:linear structure-package-introduced-at-most-once)))))

(defthm structure-library-lines-report-second-introduction
  (let ((result (bx-library-lines ground-fns hi translations wrld)))
    (implies (< 1 (structure-introduction-count name (car result) nil))
             (structure-order-notes-report-conflict-p name (mv-nth 2 result))))
  :hints (("Goal" :expand ((bx-library-lines ground-fns hi translations wrld)))))

(defthm structure-library-prefix-duplicate-or-book-conflict
  (let ((checked (bx-check-stmts library signatures names packages nil nil)))
    (implies
     (and (<= (structure-introduction-count name library nil) 1)
          (< 1 (structure-introduction-count name (append library lines) nil)))
     (structure-order-items-report-conflict-p
      name (car (bx-check-stmts lines (mv-nth 1 checked) (mv-nth 2 checked)
                                (mv-nth 3 checked) (mv-nth 4 checked) nil)))))
  :hints (("Goal"
           :use ((:instance structure-check-statements-order
                            (lines library) (earlier nil) (notes nil))
                 (:instance structure-introduction-count-of-append
                            (prefix library) (earlier nil))
                 (:instance structure-name-installed-after-introduction
                            (lines library) (earlier nil))
                 (:instance structure-package-introduced-at-most-once
                            (lines (append library lines)) (earlier nil))
                 (:instance structure-audit-reports-repeat-of-name
                            (signatures (mv-nth 1 (structure-order-scan
                                                   library signatures names packages nil)))
                            (names (mv-nth 2 (structure-order-scan
                                              library signatures names packages nil)))
                            (packages (mv-nth 3 (structure-order-scan
                                                 library signatures names packages nil)))
                            (earlier (mv-nth 4 (structure-order-scan
                                                library signatures names packages nil)))
                            (notes nil)))
           :in-theory (disable structure-introduction-count-of-append
                               (:linear structure-package-introduced-at-most-once)
                               structure-name-installed-after-introduction
                               structure-audit-reports-repeat-of-name))))

(defthm structure-combined-audit-reports-second-introduction
  (let* ((prefix (bx-check-stmts library signatures names packages nil nil))
         (extension (bx-check-stmts lines (mv-nth 1 prefix) (mv-nth 2 prefix)
                                   (mv-nth 3 prefix) (mv-nth 4 prefix) nil))
         (notes (append (bx-library-problems (append order-notes (car prefix))) (car extension))))
    (implies (< 1 (structure-introduction-count name (append library lines) nil))
             (structure-order-notes-report-conflict-p
              name (bx-note-lines (bx-select :note notes)))))
  :hints (("Goal"
           :cases ((< 1 (structure-introduction-count name library nil)))
           :use ((:instance structure-first-audit-reports-second-introduction (lines library))
                 (:instance structure-library-prefix-duplicate-or-book-conflict))
           :in-theory (disable bx-library-problems
                               structure-first-audit-reports-second-introduction
                               structure-library-prefix-duplicate-or-book-conflict))))

(defthm structure-combined-audit-retains-conflicts-in-book
  (let* ((prefix (bx-check-stmts library signatures names packages nil nil))
         (extension (bx-check-stmts lines (mv-nth 1 prefix) (mv-nth 2 prefix)
                                   (mv-nth 3 prefix) (mv-nth 4 prefix) nil))
         (notes (append (bx-library-problems (append order-notes (car prefix))) (car extension))))
    (implies (< 1 (structure-introduction-count name (append library lines) nil))
             (structure-order-notes-report-conflict-p
              name (bx-note-lines (bx-book-notes items notes boot-hi lo hi books-dir cbd wrld)))))
  :hints (("Goal" :use ((:instance structure-combined-audit-reports-second-introduction))
                  :in-theory (disable bx-library-problems
                                      structure-combined-audit-reports-second-introduction
                                      structure-note-lines-of-append structure-select-of-append))))

(defthm structure-book-lines-report-second-introduction
  (let ((result (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld)))
    (implies
     (and (structure-library-prefix-matches-p library ground-fns boot-hi wrld)
          (< 1 (structure-introduction-count name (append library (car result)) nil)))
     (structure-order-notes-report-conflict-p name (mv-nth 2 result))))
  :hints (("Goal"
           :expand ((bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
           :use ((:instance structure-matching-library-statements))
           :in-theory (disable bx-library-problems))))

; Completeness counts effective introductions, including an introduction
; in the library when the book repeats it.  An unresolved name or a
; conflicting introduction has a note that specifically names it.

(defthm structure-library-lines-complete-or-note
  (implies (and (structure-range-recordsp wrld 0 hi)
                (structure-range-namep name record 0 hi wrld)
                (structure-namex-shapep record))
           (let ((result (bx-library-lines ground-fns hi translations wrld)))
             (or (structure-no-statement-due-p name record wrld)
                 (structure-library-ground-supplies-p name ground-fns)
                 (equal (structure-introduction-count name (car result) nil) 1)
                 (structure-name-has-note-p name (mv-nth 2 result)))))
  :hints (("Goal"
           :use ((:instance structure-library-lines-supply-or-note)
                 (:instance structure-name-supplied-has-an-introduction
                            (lines (car (bx-library-lines ground-fns hi translations wrld)))
                            (earlier nil))
                 (:instance structure-library-lines-report-second-introduction))
           :in-theory (disable structure-library-lines-supply-or-note
                               structure-name-supplied-has-an-introduction
                               structure-library-lines-report-second-introduction))))

(defthm structure-book-lines-complete-or-note
  (implies (and (structure-range-recordsp wrld lo hi)
                (structure-range-namep name record lo hi wrld)
                (structure-namex-shapep record)
                (structure-library-prefix-matches-p library ground-fns boot-hi wrld))
           (let ((result (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld)))
             (or (structure-no-statement-due-p name record wrld)
                 (equal (structure-introduction-count name
                                                      (append library (car result)) nil)
                        1)
                 (structure-name-has-note-p name (mv-nth 2 result)))))
  :hints (("Goal"
           :use ((:instance structure-book-lines-supply-or-note)
                 (:instance structure-name-supplied-has-an-introduction
                            (lines (append library
                                           (car (bx-book-lines ground-fns boot-hi lo hi translations
                                                               books-dir cbd wrld))))
                            (earlier nil))
                 (:instance structure-book-lines-report-second-introduction))
           :in-theory (disable structure-book-lines-supply-or-note
                               structure-name-supplied-has-an-introduction
                               structure-book-lines-report-second-introduction))))
