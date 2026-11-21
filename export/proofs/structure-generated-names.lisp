(in-package "ACL2")

(include-book "structure-name-routing")
(include-book "structure-entry-coverage")

; Record each statement that takes the given name at its creation.
; Releasing a stored bundle does not create its statements again.

(defun structure-creation-log (name pairs pending defined translations wrld)
  (declare (xargs :measure (acl2-count pairs)))
  (if (endp pairs)
      nil
    (let ((record (caar pairs))
          (enclosing (cdar pairs)))
      (mv-let (items pending1)
        (bx-event-items record enclosing pending defined translations wrld)
        (let ((held (structure-defer-items-p items enclosing pending1 wrld)))
          (append (structure-name-items name (structure-primary-items
                                              record enclosing pending defined translations wrld))
                  (structure-creation-log
                   name (cdr pairs)
                   (if held (bx-add-candidates enclosing (list (list nil :after items)) pending1)
                     pending1)
                   (bx-add-defined items defined) translations wrld)))))))

(local (in-theory (disable bx-event-items bx-items bx-add-candidates bx-add-defined
                           structure-primary-items structure-defer-items-p
                           structure-name-items structure-name-opportunity-p
                           structure-pending-names-owned-p structure-unregistered-symbol-p
                           structure-namex-shapep structure-line-supplies-p
                           structure-constraint-record-p revappend reverse)))

(defthm structure-log-step
  (implies (consp pairs)
           (let* ((record (caar pairs))
                  (enclosing (cdar pairs))
                  (result (bx-event-items record enclosing pending defined translations wrld))
                  (items (car result))
                  (pending1 (mv-nth 1 result))
                  (held (structure-defer-items-p items enclosing pending1 wrld)))
             (equal (structure-creation-log name pairs pending defined translations wrld)
                    (append (structure-name-items
                             name (structure-primary-items record enclosing pending defined
                                                           translations wrld))
                            (structure-creation-log
                             name (cdr pairs)
                             (if held
                                 (bx-add-candidates enclosing (list (list nil :after items))
                                                    pending1)
                               pending1)
                             (bx-add-defined items defined) translations wrld)))))
  :hints (("Goal" :expand ((structure-creation-log name pairs pending defined translations wrld))
                  :in-theory (disable structure-creation-log))))

(defthm structure-log-empty
  (implies (not (consp pairs))
           (equal (structure-creation-log name pairs pending defined translations wrld) nil)))

(defthm structure-length-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(local (in-theory (disable structure-creation-log)))

(defthm structure-log-bounded-by-records
  (implies (and (structure-unregistered-symbol-p name wrld)
                (structure-naming-recordsp (strip-cars pairs))
                (structure-pending-names-owned-p name pending wrld))
           (<= (len (structure-creation-log name pairs pending defined translations wrld))
               (structure-name-opportunities name (strip-cars pairs) wrld)))
  :hints (("Goal"
           :induct (structure-delivery-induction pairs pending defined translations wrld acc)
           :in-theory (disable structure-primary-items-are-limited-by-opportunity))
          ("Subgoal *1/3" :use ((:instance structure-primary-items-are-limited-by-opportunity
                                          (record (caar pairs)) (enclosing (cdar pairs)))))
          ("Subgoal *1/2" :use ((:instance structure-primary-items-are-limited-by-opportunity
                                          (record (caar pairs)) (enclosing (cdar pairs)))))))

; A statement can move from a pending bundle into an event's items or
; from those items back into a bundle.  Trace such moves back to the
; statement's creation.

(defun structure-item-in-bundles-p (item pending)
  (and (consp pending)
       (or (member-equal item (bx-later-items (cdar pending)))
           (structure-item-in-bundles-p item (cdr pending)))))

(defthm structure-item-in-a-bundle-at-a-key
  (implies (member-equal item (bx-later-items (cdr (assoc-eq root pending))))
           (structure-item-in-bundles-p item pending))
  :hints (("Goal" :induct (assoc-equal root pending)
                  :in-theory (disable bx-later-items)))
  :rule-classes nil)

(defthm structure-item-in-bundles-after-put-assoc
  (implies (and (structure-item-in-bundles-p item (put-assoc-equal root values pending))
                (not (structure-item-in-bundles-p item pending)))
           (member-equal item (bx-later-items values)))
  :hints (("Goal" :in-theory (disable bx-later-items))))

(defthm structure-put-assoc-installs-its-items
  (implies (member-equal item (bx-later-items values))
           (structure-item-in-bundles-p item (put-assoc-equal root values pending)))
  :hints (("Goal" :in-theory (disable bx-later-items))))

(defthm structure-put-assoc-preserves-an-item
  (implies (and (structure-item-in-bundles-p item pending)
                (or (not (member-equal item (bx-later-items (cdr (assoc-eq root pending)))))
                    (member-equal item (bx-later-items values))))
           (structure-item-in-bundles-p item (put-assoc-equal root values pending)))
  :hints (("Goal" :induct (put-assoc-equal root values pending)
                  :in-theory (disable bx-later-items))))

(defthm structure-item-in-bundles-after-add
  (iff (structure-item-in-bundles-p item (bx-add-candidates root values pending))
       (or (structure-item-in-bundles-p item pending)
           (member-equal item (bx-later-items values))))
  :hints (("Goal" :use ((:instance structure-item-in-a-bundle-at-a-key))
                  :in-theory (enable bx-add-candidates))))

(defthm structure-held-item-after-bundle
  (iff (structure-item-in-bundles-p item
                                   (bx-add-candidates root (list (list nil :after items)) pending))
       (or (structure-item-in-bundles-p item pending) (member-equal item items)))
  :hints (("Goal" :use ((:instance structure-item-in-bundles-after-add
                                   (values (list (list nil :after items)))))
                  :in-theory (disable structure-item-in-bundles-p))))

(defthm structure-a-formula-is-not-a-bundle
  (equal (bx-later-items (list (list name :formula term))) nil))

(defthm structure-has-no-new-bundle-after-event
  (implies (structure-item-in-bundles-p
            item (mv-nth 1 (bx-event-items record enclosing pending defined translations wrld)))
           (structure-item-in-bundles-p item pending))
  :hints (("Goal"
           :in-theory (e/d (bx-event-items)
                           (bx-ev-form bx-ev-type bx-ev-namex bx-ev-symbol-class
                            bx-names bx-add-candidates bx-program-defs bx-define-items
                            bx-stobj-items bx-choose-items bx-all-program-p bx-all-constrained-p
                            bx-some-constrained-p bx-some-program-p bx-definition-candidates
                            bx-mentions-some bx-conjuncts bx-constrain-items bx-constrainer
                            bx-formula-name bx-constrained-p bx-reserve-items bx-package-items
                            bx-names-with-content bx-names-reserved subsetp-equal fgetprop
                            structure-item-in-bundles-p bx-later-items
                            structure-event-kind structure-event-namex structure-event-class
                            structure-constraint-root constraint-info)))))

(defthm structure-name-projection-membership
  (iff (member-equal line (structure-name-items name items))
       (and (structure-line-supplies-p name line)
            (member-equal (cons :stmt line) items)))
  :hints (("Goal" :induct (structure-name-items name items)
                  :in-theory (enable structure-name-items))))

(defthm structure-event-statement-was-created-or-held
  (implies (member-equal line
                         (structure-name-items name
                                              (car (bx-event-items record enclosing pending
                                                                   defined translations wrld))))
           (or (member-equal line (structure-name-items
                                   name (structure-primary-items record enclosing pending defined
                                                                 translations wrld)))
               (structure-item-in-bundles-p (cons :stmt line) pending)))
  :hints (("Goal"
           :use ((:instance structure-event-name-items-breakdown)
                 (:instance structure-name-projection-membership
                            (items (bx-later-items
                                    (cdr (assoc-eq (structure-constraint-root record wrld)
                                                   pending)))))
                 (:instance structure-item-in-a-bundle-at-a-key
                            (item (cons :stmt line))
                            (root (structure-constraint-root record wrld))))
           :in-theory (disable structure-item-in-bundles-p bx-later-items
                               structure-constraint-root structure-name-projection-membership))))

(defthm structure-step-statement-was-created-or-carried
  (let* ((record (caar pairs))
         (enclosing (cdar pairs))
         (result (bx-event-items record enclosing pending defined translations wrld))
         (items (car result))
         (pending1 (mv-nth 1 result))
         (held (structure-defer-items-p items enclosing pending1 wrld))
         (after (if held (bx-add-candidates enclosing (list (list nil :after items)) pending1)
                  pending1))
         (item (cons :stmt line)))
    (implies (and (structure-line-supplies-p name line)
                  (or (member-equal item (if held acc (revappend items acc)))
                      (structure-item-in-bundles-p item after)))
             (or (member-equal line (structure-name-items
                                     name (structure-primary-items record enclosing pending defined
                                                                   translations wrld)))
                 (member-equal item acc)
                 (structure-item-in-bundles-p item pending))))
  :hints (("Goal" :use ((:instance structure-event-statement-was-created-or-held
                                   (record (caar pairs)) (enclosing (cdar pairs))))
                  :in-theory (disable structure-item-in-bundles-p
                                      structure-event-statement-was-created-or-held))))

(defthm structure-output-statement-was-created-or-carried
  (implies (and (structure-line-supplies-p name line)
                (member-equal (cons :stmt line)
                              (bx-items pairs pending defined translations wrld acc)))
           (or (member-equal line (structure-creation-log name pairs pending defined
                                                         translations wrld))
               (member-equal (cons :stmt line) acc)
               (structure-item-in-bundles-p (cons :stmt line) pending)))
  :hints (("Goal"
           :induct (structure-delivery-induction pairs pending defined translations wrld acc)
           :in-theory (disable structure-item-in-bundles-p
                               structure-step-statement-was-created-or-carried))
          ("Subgoal *1/3"
           :use ((:instance structure-step-statement-was-created-or-carried)))
          ("Subgoal *1/2"
           :use ((:instance structure-step-statement-was-created-or-carried)))))

; Filtering and ordering the library can only retain or rearrange
; statements from the input.

(defthm structure-member-in-output-select
  (implies key
           (iff (member-equal line (bx-select key items))
                (member-equal (cons key line) items))))

(defthm structure-ground-filter-only-removes-lines
  (implies (member-equal line (bx-not-ground lines ground))
           (member-equal line lines))
  :hints (("Goal" :induct (bx-not-ground lines ground)
                  :in-theory (disable bx-introduced subsetp-equal))))

(defthm structure-word-filter-only-removes-lines
  (implies (member-equal line (bx-words words lines))
           (member-equal line lines)))

(local (in-theory (disable hons-get hons-acons)))

(defthm structure-library-index-lookup-is-from-values
  (implies (equal (cdr (hons-get name index)) line)
           (or (not line) (member-equal line (strip-cdrs index))))
  :hints (("Goal" :induct (hons-assoc-equal name index)
                  :in-theory (enable hons-get))))

(defthm structure-index-fns-uses-only-its-line
  (iff (member-equal line (strip-cdrs (bx-index-fns fns statement acc)))
       (or (and (consp fns) (equal line statement))
           (member-equal line (strip-cdrs acc))))
  :hints (("Goal" :in-theory (enable hons-acons))))

(defthm structure-library-index-only-references-its-lines
  (implies (and (not (member-equal line statements))
                (not (member-equal line (strip-cdrs acc))))
           (not (member-equal line (strip-cdrs (bx-index statements acc)))))
  :hints (("Goal" :induct (bx-index statements acc)
                  :in-theory (disable bx-index-fns bx-introduced))))

(defthm structure-walk-only-outputs-its-lines
  (implies (and (not (member-equal line todo))
                (not (member-equal line (strip-cars stack)))
                (not (member-equal line (strip-cdrs index)))
                (not (member-equal line acc)))
           (not (member-equal line (car (bx-walk stack todo index done acc notes fuel)))))
  :hints (("Goal" :induct (bx-walk stack todo index done acc notes fuel)
                  :in-theory (disable bx-used bx-introduced))))

(defthm structure-library-order-only-outputs-input-lines
  (implies (member-equal line (car (bx-library-order lines)))
           (member-equal line lines))
  :hints (("Goal"
           :use ((:instance structure-walk-only-outputs-its-lines
                            (stack nil) (todo (bx-words '("define" "constrain" "choose") lines))
                            (index (bx-index (bx-words '("define" "constrain" "choose") lines)
                                             nil))
                            (done nil) (acc nil) (notes nil)
                            (fuel (bx-steps (bx-words '("define" "constrain" "choose") lines)))))
           :in-theory (disable bx-walk bx-steps bx-index bx-words
                               structure-walk-only-outputs-its-lines))))

; A first occurrence that introduces a name consumes a distinct line
; from any list covering the supplying statements.

(defthm structure-empty-line-supplies-no-name
  (not (structure-line-supplies-p name nil))
  :hints (("Goal" :in-theory (enable structure-line-supplies-p))))

(defun structure-untraced-supplying-line (name lines sources)
  (cond ((endp lines) nil)
        ((and (structure-line-supplies-p name (car lines))
              (not (member-equal (car lines) sources)))
         (car lines))
        (t (structure-untraced-supplying-line name (cdr lines) sources))))

(defthm structure-untraced-line-is-a-witness
  (let ((line (structure-untraced-supplying-line name lines sources)))
    (implies line
             (and (structure-line-supplies-p name line)
                  (member-equal line lines)
                  (not (member-equal line sources)))))
  :hints (("Goal" :induct (structure-untraced-supplying-line name lines sources))))

(defthm structure-untraced-line-of-append
  (equal (structure-untraced-supplying-line name (append a b) sources)
         (or (structure-untraced-supplying-line name a sources)
             (structure-untraced-supplying-line name b sources))))

(defthm structure-untraced-line-exists
  (implies (and (structure-line-supplies-p name line)
                (member-equal line lines)
                (not (member-equal line sources)))
           (structure-untraced-supplying-line name lines sources))
  :hints (("Goal" :induct (member-equal line lines)))
  :rule-classes nil)

(defthm structure-traced-line-stays-covered-in-append
  (implies (and (not (structure-untraced-supplying-line name a sources-a))
                (not (structure-untraced-supplying-line name b sources-b)))
           (not (structure-untraced-supplying-line name (append a b)
                                                  (append sources-a sources-b))))
  :hints (("Goal"
           :use ((:instance structure-untraced-line-is-a-witness
                            (lines (append a b)) (sources (append sources-a sources-b)))
                 (:instance structure-untraced-line-exists
                            (lines a) (sources sources-a)
                            (line (structure-untraced-supplying-line name (append a b)
                                                                     (append sources-a sources-b))))
                 (:instance structure-untraced-line-exists
                            (lines b) (sources sources-b)
                            (line (structure-untraced-supplying-line name (append a b)
                                                                     (append sources-a sources-b)))))
           :in-theory (disable structure-untraced-supplying-line
                               structure-untraced-line-is-a-witness
                               structure-untraced-line-of-append)))
  :rule-classes nil)

(defthm structure-set-difference-with-additional-name
  (equal (set-difference-equal sources (cons line earlier))
         (remove-equal line (set-difference-equal sources earlier)))
  :hints (("Goal" :induct (set-difference-equal sources earlier))))

(defthm structure-removing-an-item-does-not-increase-length
  (<= (len (remove-equal item items)) (len items))
  :rule-classes :linear)

(defthm structure-removing-an-existing-item-decreases-length
  (implies (member-equal item items)
           (< (len (remove-equal item items)) (len items)))
  :rule-classes :linear)

(defthm structure-count-by-available-source-lines
  (implies (not (structure-untraced-supplying-line name lines sources))
           (<= (structure-introduction-count name lines earlier)
               (len (set-difference-equal sources earlier))))
  :hints (("Goal" :induct (structure-introduction-count name lines earlier)
                  :in-theory (disable structure-line-supplies-p set-difference-equal
                                      remove-equal))))

(defthm structure-no-earlier-lines-block-source
  (equal (len (set-difference-equal sources nil)) (len sources)))

; The range hypotheses identify the event sequence and its record
; shapes.  The creation log has at most as many entries as there are
; events with an opportunity to take the name, counting inner and outer
; closing records separately.

(defun structure-range-name-log (name wrld lo hi translations)
  (structure-creation-log name (structure-range-pairs wrld lo hi)
                          nil nil translations wrld))

(defthm structure-range-log-bounded-by-opportunities
  (implies (and (structure-unregistered-symbol-p name wrld)
                (structure-naming-recordsp (structure-range-events wrld lo hi nil)))
           (<= (len (structure-range-name-log name wrld lo hi translations))
               (structure-name-opportunities name (structure-range-events wrld lo hi nil)
                                             wrld)))
  :hints (("Goal"
           :use ((:instance structure-log-bounded-by-records
                            (pairs (structure-range-pairs wrld lo hi)) (pending nil) (defined nil)))
           :in-theory (enable structure-pending-names-owned-p)))
  :rule-classes nil)

(defthm structure-statement-supplied-by-range-log
  (implies (and (structure-range-recordsp wrld lo hi)
                (structure-line-supplies-p name line)
                (member-equal line (bx-select :stmt (bx-range-items lo hi translations wrld))))
           (member-equal line (structure-range-name-log name wrld lo hi translations)))
  :hints (("Goal"
           :use ((:instance structure-output-statement-was-created-or-carried
                            (pairs (structure-range-pairs wrld lo hi))
                            (pending nil) (defined nil) (acc nil)))
           :in-theory (e/d (structure-item-in-bundles-p)
                           (structure-range-pairs structure-range-events structure-range-recordsp
                            bx-enclose bx-events structure-items-step structure-items-empty
                            structure-output-statement-was-created-or-carried))))
  :rule-classes nil)

(local (in-theory (disable structure-range-name-log structure-range-pairs structure-range-events
                           structure-range-recordsp structure-untraced-supplying-line
                           structure-name-opportunities structure-introduction-count
                           structure-untraced-line-of-append
                           bx-library-lines bx-book-lines bx-range-items bx-check-stmts
                           bx-count-lines bx-note-lines bx-not-ground bx-library-order
                           bx-enclose bx-events bx-attachment-pairs bx-world-at bx-book-notes
                           bx-library-program-order bx-ground-tables bx-ground-defines bx-runnable
                           bx-attach-lines bx-event-aids structure-library-prefix-matches-p
                           bx-select)))

(defthm structure-range-statements-traced-to-log
  (implies (structure-range-recordsp wrld lo hi)
           (not (structure-untraced-supplying-line
                 name (bx-select :stmt (bx-range-items lo hi translations wrld))
                 (structure-range-name-log name wrld lo hi translations))))
  :hints (("Goal"
           :use ((:instance structure-statement-supplied-by-range-log
                            (line (structure-untraced-supplying-line
                                   name (bx-select :stmt (bx-range-items lo hi translations wrld))
                                   (structure-range-name-log name wrld lo hi translations))))
                 (:instance structure-untraced-line-is-a-witness
                            (lines (bx-select :stmt (bx-range-items lo hi translations wrld)))
                            (sources (structure-range-name-log name wrld lo hi translations)))))))

(defthm structure-library-line-was-in-range
  (implies (member-equal line (car (bx-library-lines ground-fns hi translations wrld)))
           (member-equal line (bx-select :stmt (bx-range-items 0 hi translations wrld))))
  :hints (("Goal"
           :expand ((bx-library-lines ground-fns hi translations wrld))
           :use ((:instance structure-library-order-only-outputs-input-lines
                            (lines (bx-not-ground
                                    (bx-select :stmt (bx-range-items 0 hi translations wrld))
                                    ground-fns)))
                 (:instance structure-ground-filter-only-removes-lines
                            (lines (bx-select :stmt (bx-range-items 0 hi translations wrld)))
                            (ground ground-fns)))
           :in-theory (e/d (bx-range-items)
                           (structure-member-in-output-select
                            structure-library-order-only-outputs-input-lines
                            structure-ground-filter-only-removes-lines))))
  :rule-classes nil)

(defthm structure-library-statements-traced-to-log
  (implies (structure-range-recordsp wrld 0 hi)
           (not (structure-untraced-supplying-line
                 name (car (bx-library-lines ground-fns hi translations wrld))
                 (structure-range-name-log name wrld 0 hi translations))))
  :hints (("Goal"
           :use ((:instance structure-statement-supplied-by-range-log
                            (lo 0)
                            (line (structure-untraced-supplying-line
                                   name (car (bx-library-lines ground-fns hi translations wrld))
                                   (structure-range-name-log name wrld 0 hi translations))))
                 (:instance structure-library-line-was-in-range
                            (line (structure-untraced-supplying-line
                                   name (car (bx-library-lines ground-fns hi translations wrld))
                                   (structure-range-name-log name wrld 0 hi translations))))
                 (:instance structure-untraced-line-is-a-witness
                            (lines (car (bx-library-lines ground-fns hi translations wrld)))
                            (sources (structure-range-name-log name wrld 0 hi translations))))
           :in-theory (disable structure-member-in-output-select))))

(defthm structure-book-statements-traced-to-log
  (implies (structure-range-recordsp wrld lo hi)
           (not (structure-untraced-supplying-line
                 name (car (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
                 (structure-range-name-log name wrld lo hi translations))))
  :hints (("Goal"
           :expand ((bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
           :use ((:instance structure-range-statements-traced-to-log))
           :in-theory (e/d (bx-range-items) (structure-range-statements-traced-to-log)))))

(defthm structure-library-lines-generated-name-bound
  (implies (and (structure-range-recordsp wrld 0 hi)
                (structure-unregistered-symbol-p name wrld)
                (structure-naming-recordsp (structure-range-events wrld 0 hi nil)))
           (<= (structure-introduction-count
                name (car (bx-library-lines ground-fns hi translations wrld)) nil)
               (structure-name-opportunities name (structure-range-events wrld 0 hi nil) wrld)))
  :hints (("Goal"
           :use ((:instance structure-range-log-bounded-by-opportunities (lo 0))
                 (:instance structure-count-by-available-source-lines
                            (lines (car (bx-library-lines ground-fns hi translations wrld)))
                            (sources (structure-range-name-log name wrld 0 hi translations))
                            (earlier nil))))))

(defthm structure-matching-library-traced-to-log
  (implies (and (structure-range-recordsp wrld 0 boot-hi)
                (structure-library-prefix-matches-p library ground-fns boot-hi wrld))
           (not (structure-untraced-supplying-line
                 name library (structure-range-name-log name wrld 0 boot-hi nil))))
  :hints (("Goal" :in-theory (enable structure-library-prefix-matches-p))))

(defthm structure-book-output-generated-name-bound
  (implies (and (structure-range-recordsp wrld lo hi)
                (structure-unregistered-symbol-p name wrld)
                (structure-naming-recordsp (structure-range-events wrld lo hi nil)))
           (<= (structure-introduction-count
                name (car (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld))
                nil)
               (structure-name-opportunities name (structure-range-events wrld lo hi nil) wrld)))
  :hints (("Goal"
           :use ((:instance structure-range-log-bounded-by-opportunities)
                 (:instance structure-count-by-available-source-lines
                            (lines (car (bx-book-lines ground-fns boot-hi lo hi translations
                                                               books-dir cbd wrld)))
                            (sources (structure-range-name-log name wrld lo hi translations))
                            (earlier nil))))))

(defthm structure-book-lines-generated-name-bound
  (let ((book (car (bx-book-lines ground-fns boot-hi lo hi translations books-dir cbd wrld)))
        (library-events (structure-range-events wrld 0 boot-hi nil))
        (book-events (structure-range-events wrld lo hi nil)))
    (implies (and (structure-range-recordsp wrld 0 boot-hi)
                  (structure-range-recordsp wrld lo hi)
                  (structure-unregistered-symbol-p name wrld)
                  (structure-naming-recordsp library-events)
                  (structure-naming-recordsp book-events)
                  (structure-library-prefix-matches-p library ground-fns boot-hi wrld))
             (<= (structure-introduction-count name (append library book) nil)
                 (+ (structure-name-opportunities name library-events wrld)
                    (structure-name-opportunities name book-events wrld)))))
  :hints (("Goal"
           :use ((:instance structure-range-log-bounded-by-opportunities)
                 (:instance structure-range-log-bounded-by-opportunities
                            (lo 0) (hi boot-hi) (translations nil))
                 (:instance structure-traced-line-stays-covered-in-append
                            (a library) (sources-a (structure-range-name-log name wrld 0 boot-hi nil))
                            (b (car (bx-book-lines ground-fns boot-hi lo hi translations books-dir
                                                   cbd wrld)))
                            (sources-b (structure-range-name-log name wrld lo hi translations)))
                 (:instance structure-count-by-available-source-lines
                            (lines (append library
                                           (car (bx-book-lines ground-fns boot-hi lo hi translations
                                                               books-dir cbd wrld))))
                            (sources (append (structure-range-name-log name wrld 0 boot-hi nil)
                                             (structure-range-name-log name wrld lo hi translations)))
                            (earlier nil))))))
