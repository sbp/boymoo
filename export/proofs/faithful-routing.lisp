(in-package "ACL2")

(include-book "faithful-origin")

(local (deftheory faithful-routing-base-theory (current-theory :here)))

; An enclosure selected by the reverse scan always has an event still
; ahead in the forward scan. Each stack entry was added while processing
; that later event.

(local
 (defun faithful-owner-ahead-p (owner pairs wrld)
   (if (endp pairs)
       nil
     (or (equal owner (bx-constrainer (caar pairs) wrld))
         (faithful-owner-ahead-p owner (cdr pairs) wrld)))))

(local
 (defun faithful-enclosers-ahead-p (pairs wrld)
   (if (endp pairs)
       t
     (and (or (null (cdar pairs))
              (faithful-owner-ahead-p (cdar pairs) (cdr pairs) wrld))
          (faithful-enclosers-ahead-p (cdr pairs) wrld)))))

(local
 (defun faithful-stack-covered-p (stack pairs wrld)
   (if (endp stack)
       t
     (and (or (null (cdar stack))
              (faithful-owner-ahead-p (cdar stack) pairs wrld))
          (faithful-stack-covered-p (cdr stack) pairs wrld)))))

(local
 (defthm faithful-pop-keeps-stack-covered
   (implies (faithful-stack-covered-p stack pairs wrld)
            (faithful-stack-covered-p (bx-pop stack depth) pairs wrld))
   :hints (("Goal" :induct (bx-pop stack depth)
            :in-theory (disable faithful-owner-ahead-p)))))

(local
 (defthm faithful-first-constrainer-ahead
   (implies (and (faithful-stack-covered-p stack pairs wrld)
                 (bx-first-constrainer stack))
            (faithful-owner-ahead-p (bx-first-constrainer stack) pairs wrld))
   :hints (("Goal" :induct (bx-first-constrainer stack)
            :in-theory (disable faithful-owner-ahead-p)))))

(local
 (defthm faithful-stack-covered-after-cons
   (implies (faithful-stack-covered-p stack pairs wrld)
            (faithful-stack-covered-p stack (cons pair pairs) wrld))
   :hints (("Goal" :induct (faithful-stack-covered-p stack pairs wrld)
            :in-theory (disable bx-constrainer)))))

(local
 (defthm faithful-enclosers-ahead-of-bx-enclose
   (implies (and (faithful-enclosers-ahead-p acc wrld)
                 (faithful-stack-covered-p stack acc wrld))
            (faithful-enclosers-ahead-p (bx-enclose evs stack acc wrld) wrld))
   :hints (("Goal" :induct (bx-enclose evs stack acc wrld)
            :in-theory (disable bx-constrainer bx-ev-depth
                                bx-pop bx-first-constrainer)))))

; Once deferred, an item remains in its bucket until the event that
; releases it. Adding formula candidates does not remove deferred items.

(local
 (defthm faithful-lookup-of-put
   (equal (cdr (assoc-equal owner (put-assoc-equal other candidates pending)))
          (if (equal owner other)
              candidates
            (cdr (assoc-equal owner pending))))
   :hints (("Goal" :induct (put-assoc-equal other candidates pending)))))

(local
 (defthm faithful-bucket-item-kept-by-candidates
   (implies (member-equal item (bx-later-items (cdr (assoc-equal owner pending))))
            (member-equal item
                          (bx-later-items
                           (cdr (assoc-equal owner
                                             (bx-add-candidates other candidates
                                                                pending))))))
   :hints (("Goal" :in-theory (disable bx-later-items put-assoc-equal assoc-equal)))))

(local
 (defthm faithful-bucket-item-kept-by-event
   (implies (member-equal item (bx-later-items (cdr (assoc-equal owner pending))))
            (member-equal
             item
             (bx-later-items
              (cdr (assoc-equal owner
                                (mv-nth 1 (bx-event-items ev encl pending defined
                                                           translations wrld)))))))
   :hints (("Goal"
            :in-theory (disable bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                                bx-names bx-constrainer bx-constrain-items
                                bx-program-defs bx-all-program-p bx-some-program-p
                                bx-all-constrained-p bx-some-constrained-p
                                bx-constrained-p bx-add-candidates bx-choose-items
                                bx-definition-candidates bx-define-items bx-stobj-items
                                bx-reserve-items bx-package-items bx-names-with-content
                                bx-names-reserved bx-mentions-some bx-conjuncts
                                constraint-info fgetprop bx-later-items assoc-equal)
            :do-not-induct t))))

(local
 (defthm faithful-bucket-item-kept-by-delay
   (implies (member-equal item (bx-later-items (cdr (assoc-equal owner pending))))
            (member-equal item
                          (bx-later-items
                           (cdr (assoc-equal owner
                                             (faithful-next-pending other items
                                                                    pending wrld))))))
   :hints (("Goal" :in-theory (e/d (faithful-next-pending)
                                   (bx-add-candidates bx-later-items assoc-equal))))))

(local
 (defthm faithful-bucket-receives-delayed-item
   (implies (and (faithful-delay-items-p owner items pending wrld)
                 (member-equal item items))
            (member-equal item
                          (bx-later-items
                           (cdr (assoc-equal owner
                                             (faithful-next-pending owner items
                                                                    pending wrld))))))
   :hints (("Goal" :in-theory (e/d (faithful-next-pending)
                                   (put-assoc-equal assoc-equal))))))

(local
 (defthm faithful-constrainer-has-signature
   (implies (bx-constrainer ev wrld)
            (and (equal (bx-ev-type ev) 'encapsulate)
                 (consp (bx-names (bx-ev-namex ev)))))
   :hints (("Goal" :in-theory (disable bx-ev-type bx-ev-namex constraint-info)))))

(local
 (defthm faithful-constrainer-releases-bucket-item
   (implies (and (bx-constrainer ev wrld)
                 (member-equal item
                               (bx-later-items (cdr (assoc-equal
                                                     (bx-constrainer ev wrld)
                                                     pending)))))
            (member-equal item
                          (mv-nth 0 (bx-event-items ev encl pending defined
                                                     translations wrld))))
   :hints (("Goal"
            :use faithful-event-items-split
            :in-theory (disable bx-event-items bx-ev-type bx-ev-namex bx-names
                                bx-constrainer assoc-equal bx-later-items)
            :do-not-induct t))))

; Track a deferred item only if its releasing event is still ahead.
; A released item can in turn be deferred to an outer encapsulate.

(local
 (defun faithful-item-waiting-p (item pairs pending wrld)
   (if (endp pairs)
       nil
     (let ((owner (bx-constrainer (caar pairs) wrld)))
       (or (and owner
                (member-equal item (bx-later-items (cdr (assoc-equal owner pending)))))
           (faithful-item-waiting-p item (cdr pairs) pending wrld))))))

(local
 (defthm faithful-waiting-for-owner-ahead
   (implies (and owner
                 (faithful-owner-ahead-p owner pairs wrld)
                 (member-equal item (bx-later-items (cdr (assoc-equal owner pending)))))
            (faithful-item-waiting-p item pairs pending wrld))
   :hints (("Goal" :induct (faithful-owner-ahead-p owner pairs wrld)
            :in-theory (disable bx-constrainer assoc-equal bx-later-items)))))

(local
 (defthm faithful-item-keeps-waiting-after-event
   (implies (faithful-item-waiting-p item pairs pending wrld)
            (faithful-item-waiting-p
             item pairs
             (mv-nth 1 (bx-event-items ev encl pending defined translations wrld))
             wrld))
   :hints (("Goal" :induct (faithful-item-waiting-p item pairs pending wrld)
            :in-theory (disable bx-event-items bx-constrainer bx-later-items
                                assoc-equal member-equal)))))

(local
 (defthm faithful-item-keeps-waiting-after-delay
   (implies (faithful-item-waiting-p item pairs pending wrld)
            (faithful-item-waiting-p
             item pairs (faithful-next-pending encl items pending wrld) wrld))
   :hints (("Goal" :induct (faithful-item-waiting-p item pairs pending wrld)
            :in-theory (disable faithful-next-pending bx-constrainer bx-later-items
                                assoc-equal member-equal)))))

(local
 (defthm faithful-delay-has-enclosure
   (implies (faithful-delay-items-p encl items pending wrld) encl)
   :hints (("Goal" :in-theory (enable faithful-delay-items-p)))
   :rule-classes :forward-chaining))

(local
 (defthm faithful-item-is-placed-or-waits
   (implies (and (member-equal item items)
                 (or (not (faithful-delay-items-p encl items pending wrld))
                     (faithful-owner-ahead-p encl remaining wrld)))
            (if (faithful-delay-items-p encl items pending wrld)
                (faithful-item-waiting-p
                 item remaining (faithful-next-pending encl items pending wrld) wrld)
              (member-equal item (revappend items acc))))
   :hints (("Goal"
            :use ((:instance faithful-waiting-for-owner-ahead
                             (owner encl)
                             (pairs remaining)
                             (pending (faithful-next-pending encl items pending wrld))))
            :in-theory (disable faithful-item-waiting-p faithful-owner-ahead-p
                                assoc-equal bx-later-items member-equal revappend)
            :do-not-induct t))))

(local
 (defund faithful-item-in-traversal-p (item pairs pending defined translations wrld acc)
   (or (member-equal item acc)
       (faithful-item-waiting-p item pairs pending wrld)
       (faithful-item-origin item pairs pending defined translations wrld))))

(local
 (defthmd faithful-item-advances
   (implies (and (consp pairs)
                 (faithful-enclosers-ahead-p pairs wrld)
                 (faithful-item-in-traversal-p
                  item pairs pending defined translations wrld acc))
            (mv-let (items after-event)
              (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld)
              (faithful-item-in-traversal-p
               item (cdr pairs)
               (faithful-next-pending (cdar pairs) items after-event wrld)
               (bx-add-defined items defined) translations wrld
               (if (faithful-delay-items-p (cdar pairs) items after-event wrld)
                   acc
                 (revappend items acc)))))
   :hints (("Goal"
            :use ((:instance faithful-constrainer-releases-bucket-item
                             (ev (caar pairs)) (encl (cdar pairs)))
                  (:instance faithful-item-is-placed-or-waits
                             (encl (cdar pairs))
                             (items (mv-nth 0 (bx-event-items
                                               (caar pairs) (cdar pairs)
                                               pending defined translations wrld)))
                             (pending (mv-nth 1 (bx-event-items
                                                 (caar pairs) (cdar pairs)
                                                 pending defined translations wrld)))
                             (remaining (cdr pairs))))
            :expand ((faithful-item-origin item pairs pending defined translations wrld)
                     (faithful-item-waiting-p item pairs pending wrld)
                     (faithful-enclosers-ahead-p pairs wrld))
            :in-theory (e/d (faithful-item-in-traversal-p)
                            (bx-event-items bx-add-defined bx-constrainer
                             faithful-owner-ahead-p faithful-item-waiting-p
                             faithful-item-origin faithful-enclosers-ahead-p
                             assoc-equal bx-later-items member-equal revappend))
            :do-not-induct t))))

(local
 (defun faithful-routing-induction (pairs pending defined translations wrld acc)
   (if (endp pairs)
       acc
     (mv-let (items after-event)
       (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld)
       (faithful-routing-induction
        (cdr pairs) (faithful-next-pending (cdar pairs) items after-event wrld)
        (bx-add-defined items defined) translations wrld
        (if (faithful-delay-items-p (cdar pairs) items after-event wrld)
            acc
          (revappend items acc)))))))

(local
 (defthm faithful-revappend-preserves-true-listp
   (implies (true-listp acc)
            (true-listp (revappend items acc)))
   :hints (("Goal" :induct (revappend items acc) :in-theory (enable revappend)))))

(local
 (defthm faithful-item-at-end-of-traversal
   (implies (and (faithful-enclosers-ahead-p pairs wrld)
                 (true-listp acc)
                 (faithful-item-in-traversal-p
                  item pairs pending defined translations wrld acc))
            (member-equal item (bx-items pairs pending defined translations wrld acc)))
   :hints (("Goal"
            :induct (faithful-routing-induction pairs pending defined translations wrld acc)
            :in-theory (e/d (faithful-bx-items-step reverse)
                            (bx-items bx-event-items bx-add-defined bx-constrainer
                             faithful-owner-ahead-p faithful-item-origin member-equal revappend)))
           ("Subgoal *1/2" :use faithful-item-advances)
           ("Subgoal *1/1"
            :in-theory (enable faithful-item-in-traversal-p faithful-item-origin)))))

(defthm faithful-range-retains-originating-item
  (implies (faithful-item-origin
            item (bx-enclose (reverse (bx-events wrld lo hi nil)) nil nil wrld)
            nil nil translations wrld)
           (member-equal item (bx-range-items lo hi translations wrld)))
  :hints (("Goal"
           :in-theory (e/d (faithful-item-in-traversal-p)
                           (bx-items bx-enclose bx-events faithful-item-origin))
           :do-not-induct t))
  :rule-classes nil)

; Both entries carry all range notes to the notes result. The book entry
; also carries all range statements to the statement result.

(local (in-theory (disable faithful-member-of-bx-select)))

(local
 (defthm faithful-bx-select-keeps-item
   (implies (member-equal (cons key data) items)
            (member-equal data (bx-select key items)))
   :hints (("Goal" :induct (bx-select key items)))
   :rule-classes nil))

(local
 (defthm faithful-bx-note-lines-keep-note
   (implies (member-equal (list key data) notes)
            (member-equal (list "note" (list key data)) (bx-note-lines notes)))
   :hints (("Goal" :induct (bx-note-lines notes)))))

(local
 (defthm faithful-bx-select-notes-of-append
   (implies (member-equal (list :note key data) items)
            (member-equal (list key data) (bx-select :note (append items tail))))
   :hints (("Goal"
            :use ((:instance faithful-bx-select-keeps-item
                             (key :note) (data (list key data))
                             (items (append items tail))))
            :in-theory (disable bx-select binary-append member-equal)))))

(defthm faithful-book-retains-range-statement
  (implies (member-equal (cons :stmt line) (bx-range-items lo hi translations wrld))
           (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir cbd
                                                       wrld))))
  :hints (("Goal"
           :use ((:instance faithful-bx-select-keeps-item
                            (key :stmt) (data line)
                            (items (bx-range-items lo hi translations wrld))))
           :in-theory (set-difference-theories
                       (theory 'faithful-routing-base-theory)
                       '(bx-range-items bx-items bx-enclose bx-events
                         bx-library-order bx-not-ground bx-ground-tables
                         bx-select bx-check-stmts bx-library-problems
                         bx-book-notes bx-attachment-pairs bx-attach-lines
                         bx-runnable bx-note-lines bx-event-aids
                         bx-world-at bx-count-lines faithful-member-of-bx-select))
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-book-retains-range-note
  (implies (member-equal (list :note key data) (bx-range-items lo hi translations wrld))
           (member-equal (list "note" (list key data))
                         (mv-nth 2 (bx-book-lines ground boot-hi lo hi translations
                                                  books-dir cbd wrld))))
  :hints (("Goal"
           :in-theory (disable bx-range-items bx-items bx-enclose bx-events
                               bx-library-order bx-not-ground bx-ground-tables
                               bx-select bx-check-stmts bx-library-problems
                               bx-attachment-pairs bx-attach-lines bx-book-ttags
                               bx-runnable bx-note-lines bx-event-aids bx-world-at
                               bx-count-lines bx-skipped bx-marked-books
                               binary-append fgetprop member-equal)
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-library-retains-range-note
  (implies (member-equal (list :note key data) (bx-range-items 0 hi translations wrld))
           (member-equal (list "note" (list key data))
                         (mv-nth 2 (bx-library-lines ground hi translations wrld))))
  :hints (("Goal"
           :in-theory (disable bx-items bx-enclose bx-events bx-library-order
                               bx-not-ground bx-ground-tables bx-select
                               bx-check-stmts bx-attachment-pairs bx-attach-lines
                               bx-runnable bx-note-lines bx-ground-defines
                               bx-library-program-order bx-count-lines
                               binary-append member-equal)
           :do-not-induct t))
  :rule-classes nil)

; The context of the first selected occurrence of an event is the pair
; of tables it receives and the owner of its enclosing constraint.

(defun faithful-event-context (event pairs pending defined translations wrld)
  (if (endp pairs)
      nil
    (if (equal event (caar pairs))
        (list (cdar pairs) pending defined)
      (mv-let (items after-event)
        (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld)
        (faithful-event-context
         event (cdr pairs) (faithful-next-pending (cdar pairs) items after-event wrld)
         (bx-add-defined items defined) translations wrld)))))

(defund faithful-range-event-context (event lo hi translations wrld)
  (faithful-event-context
   event (bx-enclose (reverse (bx-events wrld lo hi nil)) nil nil wrld)
   nil nil translations wrld))

(local
 (defthm faithful-event-context-exists
   (implies (member-equal event (strip-cars pairs))
            (faithful-event-context event pairs pending defined translations wrld))
   :hints (("Goal"
            :induct (faithful-event-context event pairs pending defined translations wrld)
            :in-theory (disable bx-event-items bx-add-defined)))))

(local
 (defthm faithful-event-kept-by-enclose
   (implies (or (member-equal event events)
                (member-equal event (strip-cars acc)))
            (member-equal event (strip-cars (bx-enclose events stack acc wrld))))
   :hints (("Goal" :induct (bx-enclose events stack acc wrld)
            :in-theory (disable bx-ev-depth bx-ev-type bx-pop bx-first-constrainer
                                bx-constrainer)))))

(local
 (defthm faithful-event-kept-by-reverse
   (implies (and (not (stringp events)) (member-equal event events))
            (member-equal event (reverse events)))
   :hints (("Goal" :in-theory (enable reverse)))))

(defthm faithful-context-of-range-event
  (implies (member-equal event (bx-events wrld lo hi nil))
           (and (faithful-range-event-context event lo hi translations wrld)
                (faithful-event-landmark-p event wrld)))
  :hints (("Goal"
           :use faithful-event-landmark-of-range
           :in-theory (e/d (faithful-range-event-context)
                           (bx-events bx-enclose faithful-event-context reverse))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm faithful-direct-event-item-is-raw
   (implies (member-equal item
                          (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                             translations wrld)))
            (member-equal item
                          (mv-nth 0 (bx-event-items ev encl pending defined
                                                     translations wrld))))
   :hints (("Goal"
            :use faithful-event-items-split
            :in-theory (disable bx-event-items bx-ev-type bx-ev-namex bx-names
                                bx-constrainer assoc-equal bx-later-items)
            :do-not-induct t))))

(local
 (defthm faithful-context-item-originates
   (let ((context (faithful-event-context event pairs pending defined translations wrld)))
     (implies (and context
                   (member-equal item
                                 (mv-nth 0 (faithful-direct-event
                                            event (car context) (cadr context)
                                            (caddr context) translations wrld))))
              (faithful-item-origin item pairs pending defined translations wrld)))
   :hints (("Goal"
            :induct (faithful-event-context event pairs pending defined translations wrld)
            :in-theory (disable bx-event-items bx-add-defined member-equal))
           ("Subgoal *1/2"
            :use ((:instance faithful-direct-event-item-is-raw
                             (ev (caar pairs)) (encl (cdar pairs))))
            :expand ((faithful-item-origin item pairs pending defined translations wrld))))))

(defthm faithful-context-item-retained
  (let ((context (faithful-range-event-context event lo hi translations wrld)))
    (implies (and context
                  (member-equal item
                                (mv-nth 0 (faithful-direct-event
                                           event (car context) (cadr context)
                                           (caddr context) translations wrld))))
             (member-equal item (bx-range-items lo hi translations wrld))))
  :hints (("Goal"
           :use faithful-range-retains-originating-item
           :in-theory (e/d (faithful-range-event-context)
                           (bx-range-items bx-items bx-enclose bx-events
                            faithful-event-context faithful-item-origin))
           :do-not-induct t))
  :rule-classes nil)

; The library orders its constraints with the other function
; introductions. A line tracked by the walk reaches the output
; unless the walk reports that ordering was incomplete.

(local
 (defund faithful-walk-tracks-line-p (line stack todo done acc notes)
   (or (member-equal line acc)
       (member-equal (list :note "order of the library not completed" nil) notes)
       (and (not (eq (cdr (hons-get line done)) t))
            (or (not (eq (cdr (hons-get line done)) :pending))
                (member-equal line (strip-cars stack)))
            (or (member-equal line todo)
                (member-equal line (strip-cars stack)))))))

(local
 (defthm faithful-hons-get-after-add
   (equal (cdr (hons-get line (hons-acons other value done)))
          (if (equal line other) value (cdr (hons-get line done))))
   :hints (("Goal" :in-theory (enable hons-get hons-acons hons-assoc-equal)))))

(local
 (defthm faithful-library-walk-places-or-notes
   (implies (and (true-listp acc)
                 (faithful-walk-tracks-line-p line stack todo done acc notes))
            (mv-let (ordered diagnostics)
              (bx-walk stack todo index done acc notes fuel)
              (or (member-equal line ordered)
                  (member-equal (list :note "order of the library not completed" nil)
                                diagnostics))))
   :hints (("Goal"
            :induct (bx-walk stack todo index done acc notes fuel)
            :in-theory (e/d (faithful-walk-tracks-line-p reverse)
                            (bx-used bx-introduced hons-get hons-acons)))
           ("Subgoal *1/1" :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-constraint-kept-by-ground-filter
   (implies (and (equal (car line) "constrain")
                 (member-equal line stmts))
            (member-equal line (bx-not-ground stmts ground)))
   :hints (("Goal" :induct (bx-not-ground stmts ground)
            :in-theory (disable bx-introduced)))))

(local
 (defthm faithful-constraint-kept-by-word-filter
   (implies (and (equal (car line) "constrain")
                 (member-equal line stmts))
            (member-equal line (bx-words '("define" "constrain" "choose") stmts)))
   :hints (("Goal"
            :induct (bx-words '("define" "constrain" "choose") stmts)))))

(local
 (defthm faithful-library-order-places-constraint-or-notes
   (implies (and (equal (car line) "constrain") (member-equal line stmts))
            (mv-let (ordered diagnostics)
              (bx-library-order stmts)
              (or (member-equal line ordered)
                  (member-equal (list :note "order of the library not completed" nil)
                                diagnostics))))
   :hints (("Goal"
            :use ((:instance faithful-library-walk-places-or-notes
                             (stack nil) (done nil) (acc nil) (notes nil)
                             (todo (bx-words '("define" "constrain" "choose") stmts))
                             (index (bx-index (bx-words '("define" "constrain" "choose")
                                                        stmts) nil))
                             (fuel (bx-steps (bx-words '("define" "constrain" "choose")
                                                       stmts)))))
            :in-theory (e/d (faithful-walk-tracks-line-p hons-get hons-assoc-equal)
                            (bx-walk bx-index bx-steps bx-used bx-introduced
                             bx-words binary-append member-equal))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-bx-select-notes-of-append-middle
   (implies (member-equal (list :note key data) notes)
            (member-equal (list key data) (bx-select :note (append head notes tail))))
   :hints (("Goal"
            :use ((:instance faithful-bx-select-keeps-item
                             (key :note) (data (list key data))
                             (items (append head notes tail))))
            :in-theory (disable bx-select binary-append member-equal)))))

(defthm faithful-library-retains-range-constraint-or-note
  (implies (and (equal (car line) "constrain")
                (member-equal (cons :stmt line) (bx-range-items 0 hi translations wrld)))
           (mv-let (stmts program notes)
             (bx-library-lines ground hi translations wrld)
             (declare (ignore program))
             (or (member-equal line stmts)
                 (member-equal (list "note" (list "order of the library not completed" nil))
                               notes))))
  :hints (("Goal"
           :use ((:instance faithful-bx-select-keeps-item
                            (key :stmt) (data line)
                            (items (bx-range-items 0 hi translations wrld)))
                 (:instance faithful-library-order-places-constraint-or-notes
                            (stmts (bx-not-ground
                                    (bx-select :stmt (bx-range-items 0 hi translations wrld))
                                    ground))))
           :in-theory (disable bx-items bx-enclose bx-events bx-library-order
                               bx-not-ground bx-ground-tables bx-select
                               bx-check-stmts bx-attachment-pairs bx-attach-lines
                               bx-runnable bx-note-lines bx-ground-defines
                               bx-library-program-order bx-count-lines bx-introduced
                               binary-append member-equal)
           :do-not-induct t))
  :rule-classes nil)
