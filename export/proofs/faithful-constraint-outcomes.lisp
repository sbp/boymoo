(in-package "ACL2")

(include-book "faithful-constraints")
(include-book "faithful-routing")

; A group is reported in a statement or in a note listing its siblings.
; The library can also report incomplete ordering for the library as a
; whole.

(defun faithful-constraint-report-present-p (kind owner lines wrld)
  (if (endp lines)
      nil
    (or (case kind
          (:statement (faithful-constraint-statement-for-p (car lines) owner wrld))
          (:missing-label (faithful-constraint-missing-name-note-for-p (car lines)
                                                                       owner wrld)))
        (faithful-constraint-report-present-p kind owner (cdr lines) wrld))))

(local
 (defthm faithful-member-supplies-constraint-report
   (implies (and (member-equal line lines)
                 (case kind
                   (:statement (faithful-constraint-statement-for-p line owner wrld))
                   (:missing-label (faithful-constraint-missing-name-note-for-p
                                    line owner wrld))))
            (faithful-constraint-report-present-p kind owner lines wrld))
   :hints (("Goal" :induct (member-equal line lines)))))

; The signed event's result survives deferred release in the range.

(local
 (defund faithful-event-constraint-item (event lo hi translations wrld)
   (let* ((signature (faithful-event-names event))
          (owner (faithful-constraint-owner (car signature) wrld))
          (context (faithful-range-event-context event lo hi translations wrld)))
     (faithful-constraint-report-item signature owner (cadr context) wrld))))

(local
 (defthm faithful-range-contains-constraint-report
   (let* ((signature (faithful-event-names event))
          (owner (faithful-constraint-owner (car signature) wrld))
          (item (faithful-event-constraint-item event lo hi translations wrld)))
     (implies (and (member-equal event (bx-events wrld lo hi nil))
                   (eq (access-event-tuple-type event) 'encapsulate)
                   (consp signature)
                   (plist-worldp-with-formals wrld)
                   (faithful-constraint-world-p wrld))
              (and (member-equal item (bx-range-items lo hi translations wrld))
                   (or (and (eq (car item) :stmt)
                            (faithful-constraint-statement-for-p (cdr item) owner wrld))
                       (and (eq (car item) :note)
                            (faithful-constraint-missing-name-note-for-p
                             (list "note" (cdr item)) owner wrld))))))
   :hints (("Goal"
            :use (faithful-context-of-range-event
                  (:instance faithful-context-item-retained
                             (item (faithful-event-constraint-item
                                    event lo hi translations wrld)))
                  (:instance faithful-constraint-report-of-landmark
                             (ev event)
                             (encl (car (faithful-range-event-context
                                         event lo hi translations wrld)))
                             (pending (cadr (faithful-range-event-context
                                             event lo hi translations wrld)))
                             (defined (caddr (faithful-range-event-context
                                              event lo hi translations wrld)))))
            :in-theory (e/d (faithful-event-constraint-item)
                            (access-event-tuple-type faithful-event-names bx-events
                             bx-range-items faithful-constraint-report-present-p
                             plist-worldp-with-formals))
            :do-not-induct t))
   :rule-classes nil))

; Every retained signed event has an entry-level statement or note.

(local
 (defthm faithful-constraint-item-as-note
   (implies (and (eq (car item) :note)
                 (faithful-constraint-missing-name-note-for-p
                  (list "note" (cdr item)) owner wrld))
            (equal (list :note (cadr item) (caddr item)) item))
   :hints (("Goal" :in-theory (enable faithful-constraint-missing-name-note-for-p
                                     faithful-missing-label-note-covers-p)))))

(local
 (defthm faithful-constraint-item-as-statement
   (implies (eq (car item) :stmt)
            (equal (cons :stmt (cdr item)) item))))

(local
 (defthm faithful-book-keeps-constraint-report
   (implies (and (member-equal item (bx-range-items lo hi translations wrld))
                 (or (and (eq (car item) :stmt)
                          (faithful-constraint-statement-for-p (cdr item) owner wrld))
                     (and (eq (car item) :note)
                          (faithful-constraint-missing-name-note-for-p
                           (list "note" (cdr item)) owner wrld))))
            (mv-let (statements program notes aids)
              (bx-book-lines ground boot-hi lo hi translations books-dir cbd wrld)
              (declare (ignore program aids))
              (or (faithful-constraint-report-present-p :statement owner statements wrld)
                  (faithful-constraint-report-present-p :missing-label owner notes wrld))))
   :hints (("Goal"
            :use ((:instance faithful-book-retains-range-statement
                             (line (cdr item)))
                  (:instance faithful-book-retains-range-note
                             (key (cadr item)) (data (caddr item)))
                  (:instance faithful-member-supplies-constraint-report
                             (kind :statement) (line (cdr item))
                             (lines (mv-nth 0 (bx-book-lines
                                               ground boot-hi lo hi translations books-dir
                                               cbd wrld))))
                  (:instance faithful-member-supplies-constraint-report
                             (kind :missing-label) (line (list "note" (cdr item)))
                             (lines (mv-nth 2 (bx-book-lines
                                               ground boot-hi lo hi translations books-dir
                                               cbd wrld)))))
            :in-theory (e/d (faithful-constraint-missing-name-note-for-p
                             faithful-missing-label-note-covers-p)
                            (bx-book-lines bx-range-items
                             faithful-constraint-report-present-p
                             faithful-member-supplies-constraint-report))
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-book-constraint-statement-or-note
  (implies (and (member-equal event (bx-events wrld lo hi nil))
                (eq (access-event-tuple-type event) 'encapsulate)
                (consp (faithful-event-names event))
                (plist-worldp-with-formals wrld)
                (faithful-constraint-world-p wrld))
           (let ((owner (faithful-constraint-owner
                         (car (faithful-event-names event)) wrld)))
             (mv-let (statements program notes aids)
               (bx-book-lines ground boot-hi lo hi translations books-dir cbd wrld)
               (declare (ignore program aids))
               (or (faithful-constraint-report-present-p :statement owner statements wrld)
                   (faithful-constraint-report-present-p :missing-label owner notes wrld)))))
  :hints (("Goal"
           :use (faithful-range-contains-constraint-report
                 (:instance faithful-book-keeps-constraint-report
                            (item (faithful-event-constraint-item
                                   event lo hi translations wrld))
                            (owner (faithful-constraint-owner
                                    (car (faithful-event-names event)) wrld))))
           :in-theory (disable bx-book-lines bx-events bx-range-items
                               access-event-tuple-type faithful-event-names
                               faithful-constraint-report-present-p plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm faithful-report-statement-is-constraint
   (implies (faithful-constraint-statement-for-p line owner wrld)
            (equal (car line) "constrain"))
   :hints (("Goal" :in-theory (enable faithful-constraint-statement-for-p)))
   :rule-classes :forward-chaining))

(local
 (defthm faithful-library-keeps-constraint-report
   (implies (and (member-equal item (bx-range-items 0 hi translations wrld))
                 (or (and (eq (car item) :stmt)
                          (faithful-constraint-statement-for-p (cdr item) owner wrld))
                     (and (eq (car item) :note)
                          (faithful-constraint-missing-name-note-for-p
                           (list "note" (cdr item)) owner wrld))))
            (mv-let (statements program notes)
              (bx-library-lines ground hi translations wrld)
              (declare (ignore program))
              (or (faithful-constraint-report-present-p :statement owner statements wrld)
                  (faithful-constraint-report-present-p :missing-label owner notes wrld)
                  (member-equal '("note" ("order of the library not completed" nil)) notes))))
   :hints (("Goal"
            :use ((:instance faithful-library-retains-range-constraint-or-note
                             (line (cdr item)))
                  (:instance faithful-library-retains-range-note
                             (key (cadr item)) (data (caddr item)))
                  (:instance faithful-member-supplies-constraint-report
                             (kind :statement) (line (cdr item))
                             (lines (mv-nth 0 (bx-library-lines ground hi translations wrld))))
                  (:instance faithful-member-supplies-constraint-report
                             (kind :missing-label) (line (list "note" (cdr item)))
                             (lines (mv-nth 2 (bx-library-lines ground hi translations wrld)))))
            :in-theory (e/d (faithful-constraint-missing-name-note-for-p
                             faithful-missing-label-note-covers-p)
                            (bx-library-lines bx-range-items bx-introduced
                             faithful-constraint-report-present-p
                             faithful-member-supplies-constraint-report))
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-library-constraint-statement-or-note
  (implies (and (member-equal event (bx-events wrld 0 hi nil))
                (eq (access-event-tuple-type event) 'encapsulate)
                (consp (faithful-event-names event))
                (plist-worldp-with-formals wrld)
                (faithful-constraint-world-p wrld))
           (let ((owner (faithful-constraint-owner
                         (car (faithful-event-names event)) wrld)))
             (mv-let (statements program notes)
               (bx-library-lines ground hi translations wrld)
               (declare (ignore program))
               (or (faithful-constraint-report-present-p :statement owner statements wrld)
                   (faithful-constraint-report-present-p :missing-label owner notes wrld)
                   (member-equal '("note" ("order of the library not completed" nil)) notes)))))
  :hints (("Goal"
           :use ((:instance faithful-range-contains-constraint-report (lo 0))
                 (:instance faithful-library-keeps-constraint-report
                            (item (faithful-event-constraint-item
                                   event 0 hi translations wrld))
                            (owner (faithful-constraint-owner
                                    (car (faithful-event-names event)) wrld))))
           :in-theory (disable bx-library-lines bx-events bx-range-items
                               access-event-tuple-type faithful-event-names
                               faithful-constraint-report-present-p plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

; The names available at the naming step are all reported when a
; formula has no label.

(defund faithful-event-constraint-formulas (event lo hi translations wrld)
  (let* ((owner (faithful-constraint-owner (car (faithful-event-names event)) wrld))
         (context (faithful-range-event-context event lo hi translations wrld)))
    (faithful-constraint-report-formulas owner (cadr context) wrld)))

(defun faithful-exhausted-constraint-noted-p (names notes)
  (if (endp notes)
      nil
    (or (faithful-missing-label-note-covers-p (car notes) names)
        (faithful-exhausted-constraint-noted-p names (cdr notes)))))

(local
 (defthm faithful-note-member-covers-names
   (implies (and (member-equal note notes)
                 (faithful-missing-label-note-covers-p note names))
            (faithful-exhausted-constraint-noted-p names notes))
   :hints (("Goal" :induct (member-equal note notes)))
   :rule-classes nil))

(local
 (defthm faithful-rebuild-exhaustion-note
   (implies (and (eq (car item) :note)
                 (faithful-missing-label-note-covers-p (list "note" (cdr item)) names))
            (and (equal (list :note (cadr item) (caddr item)) item)
                 (equal (list (cadr item) (caddr item)) (cdr item))))
   :hints (("Goal" :in-theory (enable faithful-missing-label-note-covers-p)))
   :rule-classes nil))

(local
 (defthm faithful-exhausted-range-note
   (let* ((signature (faithful-event-names event))
          (owner (faithful-constraint-owner (car signature) wrld))
          (formulas (faithful-event-constraint-formulas event lo hi translations wrld))
          (item (faithful-event-constraint-item event lo hi translations wrld))
          (names (faithful-constraint-note-names (faithful-constraint-siblings owner wrld)
                                                  formulas)))
     (implies (and (member-equal event (bx-events wrld lo hi nil))
                   (eq (access-event-tuple-type event) 'encapsulate)
                   (consp signature)
                   (plist-worldp-with-formals wrld)
                   (faithful-constraint-world-p wrld)
                   (member-equal nil (strip-cars formulas)))
              (and (member-equal (list :note (cadr item) (caddr item))
                                 (bx-range-items lo hi translations wrld))
                   (faithful-missing-label-note-covers-p
                    (list "note" (list (cadr item) (caddr item))) names))))
   :hints (("Goal"
            :use (faithful-context-of-range-event
                  faithful-range-contains-constraint-report
                  (:instance faithful-constraint-record-of-event (ev event))
                  (:instance faithful-rebuild-exhaustion-note
                             (item (faithful-event-constraint-item event lo hi translations wrld))
                             (names (faithful-constraint-note-names
                                     (faithful-constraint-siblings
                                      (faithful-constraint-owner
                                       (car (faithful-event-names event)) wrld)
                                      wrld)
                                     (faithful-event-constraint-formulas
                                      event lo hi translations wrld))))
                  (:instance faithful-exhausted-constraint-report
                             (signature (faithful-event-names event))
                             (owner (faithful-constraint-owner
                                     (car (faithful-event-names event)) wrld))
                             (pending (cadr (faithful-range-event-context
                                             event lo hi translations wrld)))))
            :in-theory (e/d (faithful-event-constraint-formulas
                             faithful-event-constraint-item)
                            (bx-events bx-range-items access-event-tuple-type
                             faithful-event-names plist-worldp-with-formals))
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-book-exhausted-constraint-names-noted
  (let* ((signature (faithful-event-names event))
         (owner (faithful-constraint-owner (car signature) wrld))
         (formulas (faithful-event-constraint-formulas event lo hi translations wrld)))
    (implies (and (member-equal event (bx-events wrld lo hi nil))
                  (eq (access-event-tuple-type event) 'encapsulate)
                  (consp signature)
                  (plist-worldp-with-formals wrld)
                  (faithful-constraint-world-p wrld)
                  (member-equal nil (strip-cars formulas)))
             (faithful-exhausted-constraint-noted-p
              (faithful-constraint-note-names (faithful-constraint-siblings owner wrld)
                                              formulas)
              (mv-nth 2 (bx-book-lines ground boot-hi lo hi translations books-dir
                                       cbd wrld)))))
  :hints
  (("Goal"
    :use (faithful-exhausted-range-note
          (:instance faithful-book-retains-range-note
                     (key (cadr (faithful-event-constraint-item event lo hi translations wrld)))
                     (data (caddr (faithful-event-constraint-item event lo hi translations wrld))))
          (:instance faithful-note-member-covers-names
                     (note (list "note"
                                 (list (cadr (faithful-event-constraint-item
                                              event lo hi translations wrld))
                                       (caddr (faithful-event-constraint-item
                                               event lo hi translations wrld)))))
                     (notes (mv-nth 2 (bx-book-lines ground boot-hi lo hi translations
                                                     books-dir cbd wrld)))
                     (names (faithful-constraint-note-names
                             (faithful-constraint-siblings
                              (faithful-constraint-owner (car (faithful-event-names event)) wrld)
                              wrld)
                             (faithful-event-constraint-formulas event lo hi translations wrld)))))
    :in-theory (e/d (faithful-missing-label-note-covers-p)
                    (bx-book-lines bx-events bx-range-items access-event-tuple-type
                     faithful-event-names faithful-exhausted-constraint-noted-p
                     plist-worldp-with-formals))
    :do-not-induct t))
  :rule-classes nil)

(defthm faithful-library-exhausted-constraint-names-noted
  (let* ((signature (faithful-event-names event))
         (owner (faithful-constraint-owner (car signature) wrld))
         (formulas (faithful-event-constraint-formulas event 0 hi translations wrld)))
    (implies (and (member-equal event (bx-events wrld 0 hi nil))
                  (eq (access-event-tuple-type event) 'encapsulate)
                  (consp signature)
                  (plist-worldp-with-formals wrld)
                  (faithful-constraint-world-p wrld)
                  (member-equal nil (strip-cars formulas)))
             (faithful-exhausted-constraint-noted-p
              (faithful-constraint-note-names (faithful-constraint-siblings owner wrld)
                                              formulas)
              (mv-nth 2 (bx-library-lines ground hi translations wrld)))))
  :hints
  (("Goal"
    :use ((:instance faithful-exhausted-range-note (lo 0))
          (:instance faithful-library-retains-range-note
                     (key (cadr (faithful-event-constraint-item event 0 hi translations wrld)))
                     (data (caddr (faithful-event-constraint-item event 0 hi translations wrld))))
          (:instance faithful-note-member-covers-names
                     (note (list "note"
                                 (list (cadr (faithful-event-constraint-item
                                              event 0 hi translations wrld))
                                       (caddr (faithful-event-constraint-item
                                               event 0 hi translations wrld)))))
                     (notes (mv-nth 2 (bx-library-lines ground hi translations wrld)))
                     (names (faithful-constraint-note-names
                             (faithful-constraint-siblings
                              (faithful-constraint-owner (car (faithful-event-names event)) wrld)
                              wrld)
                             (faithful-event-constraint-formulas event 0 hi translations wrld)))))
    :in-theory (e/d (faithful-missing-label-note-covers-p)
                    (bx-library-lines bx-events bx-range-items access-event-tuple-type
                     faithful-event-names faithful-exhausted-constraint-noted-p
                     plist-worldp-with-formals))
    :do-not-induct t))
  :rule-classes nil)
