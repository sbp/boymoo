(in-package "ACL2")

(include-book "structure-order")
(include-book "structure-walk")

(local (in-theory (disable hons-acons hons-get structure-seen-index)))

; A repeat has no effect.  If a name is supplied somewhere, and has no
; supplying statement in the initial prefix, it is introduced somewhere.

(defthm structure-lines-supply-of-append
  (iff (structure-lines-supply-p name (append a b))
       (or (structure-lines-supply-p name a)
           (structure-lines-supply-p name b))))

(defthm structure-lines-supply-of-member
  (implies (and (member-equal line lines) (structure-line-supplies-p name line))
           (structure-lines-supply-p name lines))
  :hints (("Goal" :induct (member-equal line lines)
                  :in-theory (disable structure-line-supplies-p))))

(defthm structure-introduction-count-is-natural
  (natp (structure-introduction-count name lines earlier))
  :rule-classes :type-prescription)

(defthm structure-name-supplied-has-an-introduction
  (implies (and (structure-lines-supply-p name lines)
                (not (structure-lines-supply-p name earlier)))
           (< 0 (structure-introduction-count name lines earlier)))
  :hints (("Goal" :induct (structure-introduction-count name lines earlier)
                  :in-theory (disable structure-line-supplies-p))))

(defthm structure-already-declared-package
  (implies (and (stringp name) (structure-lines-supply-p name earlier))
           (equal (structure-introduction-count name lines earlier) 0))
  :hints (("Goal" :induct (structure-introduction-count name lines earlier)
                  :in-theory (disable structure-line-supplies-p))))

(defthm structure-package-introduced-at-most-once
  (implies (stringp name)
           (<= (structure-introduction-count name lines earlier) 1))
  :hints (("Goal" :induct (structure-introduction-count name lines earlier)
                  :in-theory (disable structure-line-supplies-p)))
  :rule-classes :linear)

; The name inventory is monotone.  After a first introduction, a later
; first occurrence of a different line using that name must conflict.

(defthm structure-name-recorded
  (iff (hons-get name (structure-record-names new names))
       (or (member-equal name new)
           (hons-get name names)))
  :hints (("Goal" :induct (structure-record-names new names)
                  :in-theory (enable structure-record-names hons-get hons-acons))))

(defthm structure-fresh-names-exclude-prior-name
  (implies (and (structure-fresh-names-p new names)
                (member-equal name new))
           (not (hons-get name names)))
  :hints (("Goal" :in-theory (enable structure-fresh-names-p)))
  :rule-classes nil)

(defthm structure-existing-name-is-not-fresh
  (implies (and (member-equal name new)
                (hons-get name names))
           (not (structure-fresh-names-p new names)))
  :hints (("Goal" :use ((:instance structure-fresh-names-exclude-prior-name))
                  :in-theory (disable structure-fresh-names-p)))
  :rule-classes ((:forward-chaining :trigger-terms ((member-equal name new)))))

(defthm structure-symbol-supplied-as-a-name
  (implies (not (stringp name))
           (iff (structure-line-supplies-p name line)
                (member-equal name (structure-names line)))))

(defthm structure-known-name-fails-order
  (implies (and (member-equal name (structure-names line))
                (hons-get name names))
           (not (structure-line-orderp line signatures names packages)))
  :hints (("Goal" :use ((:instance structure-fresh-names-exclude-prior-name
                                   (new (structure-names line))))
                  :in-theory (disable structure-names)))
  :rule-classes :rewrite)

(defthm structure-ordered-symbol-introductions
  (implies (and (not (stringp name))
                (not (car (structure-order-scan lines signatures names packages earlier))))
           (<= (structure-introduction-count name lines earlier)
               (if (hons-get name names) 0 1)))
  :hints
  (("Goal" :induct (structure-order-scan lines signatures names packages earlier)
           :in-theory (disable structure-line-supplies-p structure-names
                               structure-line-orderp structure-signatures
                               structure-record-signatures structure-record-names
                               structure-record-package))
   ("Subgoal *1/3"
    :use ((:instance structure-known-name-fails-order (line (car lines)))))))

; Order notes identify a conflict by the name that was already in use.
; A package line reports its rule as one symbol.  Other lines report a
; list of names.  Both have the same meaning for coverage.

(defun structure-name-in-order-problems-p (name problems)
  (and (consp problems)
       (or (and (eq (caar problems) :name-in-use)
                (let ((reported (cadar problems)))
                  (or (equal name reported)
                      (member-equal name reported))))
           (structure-name-in-order-problems-p name (cdr problems)))))

(defun structure-order-item-reports-conflict-p (name item)
  (and (eq (car item) :note)
       (equal (cadr item) "line that could not be admitted in order")
       (structure-name-in-order-problems-p name (caddr (caddr item)))))

(defun structure-order-items-report-conflict-p (name items)
  (and (consp items)
       (or (structure-order-item-reports-conflict-p name (car items))
           (structure-order-items-report-conflict-p name (cdr items)))))

(defun structure-library-conflicts-p (name problems)
  (and (consp problems)
       (or (and (equal (caar problems) "line that could not be admitted in order")
                (structure-name-in-order-problems-p name (caddr (cadar problems))))
           (structure-library-conflicts-p name (cdr problems)))))

(defun structure-order-notes-report-conflict-p (name notes)
  (and (consp notes)
       (or (and (equal (caar notes) "note")
                (let ((reason (caadar notes))
                      (data (cadadr (car notes))))
                  (cond ((equal reason "line that could not be admitted in order")
                         (structure-name-in-order-problems-p name (caddr data)))
                        ((equal reason "library whose lines could not be admitted in order")
                         (structure-library-conflicts-p name data))
                        (t nil))))
           (structure-order-notes-report-conflict-p name (cdr notes)))))

(defthm structure-conflict-problems-of-append
  (iff (structure-name-in-order-problems-p name (append a b))
       (or (structure-name-in-order-problems-p name a)
           (structure-name-in-order-problems-p name b))))

(defthm structure-new-names-reports-existing-name
  (iff (member-equal name (bx-new-names new names))
       (and (member-equal name new) (hons-get name names)))
  :hints (("Goal" :in-theory (enable bx-new-names))))

(defthm structure-order-check-reports-existing-name
  (implies (and (member-equal name (structure-names line))
                (hons-get name names))
           (structure-name-in-order-problems-p
            name (car (bx-check-stmt line signatures names packages))))
  :hints (("Goal" :use ((:instance structure-new-names-reports-existing-name
                                   (new (structure-names line))))
                  :in-theory (disable bx-new-names bx-def-arities bx-add-arities
                                      bx-add-names bx-packages-of bx-bad-calls-lst
                                      bx-alist bx-bodies bx-package-rule
                                      structure-new-names-reports-existing-name
                                      structure-check-new-names))))

(defthm structure-conflict-items-of-append
  (iff (structure-order-items-report-conflict-p name (append a b))
       (or (structure-order-items-report-conflict-p name a)
           (structure-order-items-report-conflict-p name b))))

(defthm structure-conflict-items-of-revappend
  (iff (structure-order-items-report-conflict-p name (revappend a b))
       (or (structure-order-items-report-conflict-p name a)
           (structure-order-items-report-conflict-p name b)))
  :hints (("Goal" :induct (revappend a b))))

(defthm structure-conflict-items-of-reverse
  (iff (structure-order-items-report-conflict-p name (reverse items))
       (structure-order-items-report-conflict-p name items))
  :hints (("Goal" :in-theory (disable revappend))))

(defthm structure-conflict-reported-by-order-item
  (iff (structure-order-item-reports-conflict-p
        name (structure-order-item line problems))
       (structure-name-in-order-problems-p name problems))
  :hints (("Goal" :in-theory (disable bx-introduced structure-name-in-order-problems-p))))

; Checking a tail preserves order notes already recorded.

(defthm structure-conflict-note-kept
  (implies (structure-order-items-report-conflict-p name notes)
           (structure-order-items-report-conflict-p
            name (car (bx-check-stmts lines signatures names packages seen notes))))
  :hints (("Goal" :induct (bx-check-stmts lines signatures names packages seen notes)
                  :in-theory (disable bx-check-stmt bx-stmt-key bx-introduced
                                      structure-order-item-reports-conflict-p
                                      structure-name-in-order-problems-p
                                      reverse))))

(defthm structure-audit-reports-repeat-of-name
  (implies
   (and (not (stringp name))
        (< (if (hons-get name names) 0 1)
           (structure-introduction-count name lines earlier)))
   (structure-order-items-report-conflict-p
    name (car (bx-check-stmts lines signatures names packages
                              (structure-seen-index earlier) notes))))
  :hints (("Goal" :induct (structure-order-induction lines signatures names packages earlier notes)
                  :in-theory (disable bx-check-stmts bx-check-stmt structure-seen-index
                                      structure-names structure-line-supplies-p
                                      structure-line-orderp structure-order-item
                                      structure-order-item-reports-conflict-p
                                      structure-name-in-order-problems-p reverse
                                      structure-record-signatures structure-record-names
                                      structure-record-package structure-signatures))))

; Certification of a book starts checking with the inventory left by the
; library.  These two lemmas account for introductions across that cut.

(defthm structure-introduction-count-of-append
  (equal (structure-introduction-count name (append prefix lines) earlier)
         (+ (structure-introduction-count name prefix earlier)
            (structure-introduction-count
             name lines
             (mv-nth 4 (structure-order-scan prefix signatures names packages earlier)))))
  :hints (("Goal" :induct (structure-order-scan prefix signatures names packages earlier)
                  :in-theory (disable structure-names structure-line-supplies-p
                                      structure-line-orderp structure-record-signatures
                                      structure-record-names structure-record-package
                                      structure-signatures))))

(defthm structure-name-installed-after-introduction
  (implies (and (not (stringp name))
                (or (hons-get name names)
                    (< 0 (structure-introduction-count name lines earlier))))
           (hons-get name
                     (mv-nth 2 (structure-order-scan lines signatures names packages
                                                     earlier))))
  :hints (("Goal" :induct (structure-order-scan lines signatures names packages earlier)
                  :in-theory (disable structure-names structure-line-supplies-p
                                      structure-line-orderp structure-record-signatures
                                      structure-record-names structure-record-package
                                      structure-signatures))))

(defthm structure-conflicts-of-selected-notes
  (implies (structure-order-items-report-conflict-p name items)
           (structure-order-notes-report-conflict-p name
                                                    (bx-note-lines (bx-select :note items))))
  :hints (("Goal" :induct (bx-select :note items)
                  :in-theory (disable structure-name-in-order-problems-p))))

(defthm structure-conflicts-in-selected-library-notes
  (iff (structure-library-conflicts-p name (bx-select :note items))
       (structure-order-items-report-conflict-p name items))
  :hints (("Goal" :induct (bx-select :note items)
                  :in-theory (disable structure-name-in-order-problems-p))))

(defthm structure-conflict-retained-in-library-wrapper
  (implies (structure-order-items-report-conflict-p name library-items)
           (structure-order-notes-report-conflict-p
            name (bx-note-lines (bx-select :note (bx-library-problems library-items)))))
  :hints (("Goal"
           :use ((:instance structure-conflicts-in-selected-library-notes (items library-items)))
           :in-theory (disable structure-order-items-report-conflict-p
                               structure-conflicts-in-selected-library-notes))))

(defthm structure-conflict-notes-of-append
  (iff (structure-order-notes-report-conflict-p name (append a b))
       (or (structure-order-notes-report-conflict-p name a)
           (structure-order-notes-report-conflict-p name b))))
