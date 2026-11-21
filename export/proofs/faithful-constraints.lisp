(in-package "ACL2")

(include-book "faithful-conjuncts")
(local (include-book "std/lists/sets" :dir :system))

; CONSTRAINT-INFO resolves ACL2's CONSTRAINT-LST-ETC property. The owner
; is the function under which the constraint itself is recorded.

(defund faithful-constraint-owner (fn wrld)
  (mv-let (owner terms origins)
    (constraint-info fn wrld)
    (declare (ignore terms origins))
    owner))

(defund faithful-stored-constraint (fn wrld)
  (mv-let (owner terms origins)
    (constraint-info fn wrld)
    (declare (ignore owner origins))
    terms))

(defund faithful-constraint-siblings (owner wrld)
  (getprop owner 'siblings nil 'current-acl2-world wrld))

(defun faithful-constraint-members-p (fns owner wrld)
  (if (endp fns)
      t
    (and (not (eq (getprop (car fns) 'formals t 'current-acl2-world wrld) t))
         (eq (faithful-constraint-owner (car fns) wrld) owner)
         (faithful-constraint-members-p (cdr fns) owner wrld))))

; These conditions connect a signature to the records ACL2 puts on the
; functions. A list of known formulas is already split into conjuncts.

(defund faithful-constraint-record-p (signature wrld)
  (if (atom signature)
      t
    (let* ((owner (faithful-constraint-owner (car signature) wrld))
           (siblings (faithful-constraint-siblings owner wrld))
           (terms (faithful-stored-constraint owner wrld)))
      (and owner
           (eq (faithful-constraint-owner owner wrld) owner)
           (subsetp-equal signature siblings)
           (faithful-constraint-members-p siblings owner wrld)
           (or (unknown-constraints-p terms)
               (faithful-flat-conjuncts-p terms))))))

(defund faithful-constraint-landmark-data-p (event wrld)
  (let ((signature (faithful-event-names event)))
    (or (atom signature)
        (and (consp (access-event-tuple-namex event))
             (faithful-constraint-record-p signature wrld)))))

(defun faithful-constraint-events-p (triples wrld)
  (if (endp triples)
      t
    (let ((event (cddar triples)))
      (and (or (not (and (eq (caar triples) 'event-landmark)
                         (eq (cadar triples) 'global-value)
                         (eq (access-event-tuple-type event) 'encapsulate)))
               (faithful-constraint-landmark-data-p event wrld))
           (faithful-constraint-events-p (cdr triples) wrld)))))

(defund faithful-constraint-world-p (wrld)
  (faithful-constraint-events-p wrld wrld))

; The names of a constraint are its sibling functions, each with its
; stored arity. For a known constraint the formulas account for exactly
; its stored conjuncts.

(defun faithful-arities-p (pairs wrld)
  (if (atom pairs)
      (null pairs)
    (let ((fn (caar pairs)))
      (and (equal (car pairs)
                  (list fn (len (getprop fn 'formals nil 'current-acl2-world wrld))))
           (faithful-arities-p (cdr pairs) wrld)))))

(defund faithful-constraint-data-p (args wrld)
  (let* ((pairs (car args))
         (formulas (cadr args))
         (names (strip-cars pairs))
         (owner (faithful-constraint-owner (car names) wrld))
         (siblings (faithful-constraint-siblings owner wrld))
         (terms (faithful-stored-constraint owner wrld)))
    (and (equal args (list pairs formulas))
         (consp names)
         owner
         (eq (faithful-constraint-owner owner wrld) owner)
         (subsetp-equal names siblings)
         (subsetp-equal siblings names)
         (faithful-constraint-members-p names owner wrld)
         (faithful-arities-p pairs wrld)
         (not (member-equal nil (strip-cars formulas)))
         (or (unknown-constraints-p terms)
             (faithful-constraint-coverage-p formulas terms)))))

; Sorting the sibling names changes neither which functions are listed
; nor the arity read for each function.

(local
 (defthm faithful-bx-arities-data
   (implies (plist-worldp-with-formals wrld)
            (faithful-arities-p (bx-arities fns wrld) wrld))
   :hints (("Goal" :in-theory (disable formals fgetprop)))))

(local
 (defthm faithful-bx-arities-names
   (equal (strip-cars (bx-arities fns wrld))
          (true-list-fix fns))
   :hints (("Goal" :in-theory (disable formals)))))

(local
 (defthm faithful-bx-insert-names
   (set-equiv (bx-insert-by-event fn fns wrld) (cons fn fns))
   :hints (("Goal"
            :in-theory (disable bx-event-number))
           ("Subgoal *1/1" :in-theory (enable set-equiv)))))

(local
 (defthm faithful-bx-sort-names
   (set-equiv (bx-sort-by-event fns wrld) fns)
   :hints (("Goal" :in-theory (disable bx-insert-by-event)))))

(local
 (defthm faithful-bx-insert-preserves-true-list
   (implies (true-listp fns)
            (true-listp (bx-insert-by-event fn fns wrld)))
   :hints (("Goal" :in-theory (disable bx-event-number)))))

(local
 (defthm faithful-bx-sort-true-list
   (true-listp (bx-sort-by-event fns wrld))
   :hints (("Goal" :in-theory (disable bx-insert-by-event)))
   :rule-classes :type-prescription))

(local
 (defthm faithful-members-of-bx-sibling-names
   (implies (subsetp-equal signature siblings)
            (set-equiv (append signature
                               (bx-sort-by-event (set-difference-eq
                                                  siblings signature) wrld))
                       siblings))
   :hints (("Goal"
            :in-theory (e/d (set-reasoning-witnesses)
                            (bx-sort-by-event))))))

(local
 (defthm faithful-member-shares-constraint
   (implies (and (faithful-constraint-members-p fns owner wrld)
                 (member-equal fn fns))
            (and (not (eq (getprop fn 'formals t 'current-acl2-world wrld) t))
                 (eq (faithful-constraint-owner fn wrld) owner)))
   :hints (("Goal" :in-theory (disable fgetprop)))
   :rule-classes nil))

(local
 (defthm faithful-subset-shares-constraint
   (implies (and (subsetp-equal a b)
                 (faithful-constraint-members-p b owner wrld))
            (faithful-constraint-members-p a owner wrld))
   :hints (("Goal" :induct (len a)
            :in-theory (disable fgetprop))
           ("Subgoal *1/1"
            :use ((:instance faithful-member-shares-constraint
                             (fn (car a)) (fns b)))))
   :rule-classes nil))

(local
 (defthm faithful-sorted-siblings-share-constraint
   (implies (and (subsetp-equal signature siblings)
                 (faithful-constraint-members-p siblings owner wrld))
            (faithful-constraint-members-p
             (append signature
                     (bx-sort-by-event (set-difference-eq siblings signature) wrld))
             owner wrld))
   :hints (("Goal"
            :use ((:instance faithful-members-of-bx-sibling-names)
                  (:instance faithful-subset-shares-constraint
                             (a (append signature
                                        (bx-sort-by-event
                                         (set-difference-eq siblings signature)
                                         wrld)))
                             (b siblings)))
            :in-theory (e/d (set-equiv)
                            (bx-sort-by-event faithful-members-of-bx-sibling-names
                             faithful-constraint-members-p))))))

; An encapsulate using a recorded signature takes its constraint from
; the owner of that signature. Notes contain no statements.

(defthm faithful-no-statement-in-formula-notes
  (not (member-equal (cons :stmt line)
                     (mv-nth 1 (bx-name-formulas lst cands c wrld))))
  :hints (("Goal"
           :use ((:instance faithful-name-formulas-notes-have-no-statement
                            (words nil))
                 (:instance faithful-statement-word-of-member
                            (items (mv-nth 1 (bx-name-formulas lst cands c wrld)))
                            (words nil)))
           :in-theory (disable bx-name-formulas
                               faithful-name-formulas-notes-have-no-statement))))

(local
 (defthm faithful-constraint-data-of-items
   (implies (and (plist-worldp-with-formals wrld)
                 (consp signature)
                 (equal owner (faithful-constraint-owner (car signature) wrld))
                 (faithful-constraint-record-p signature wrld)
                 (member-equal (cons :stmt line)
                               (faithful-direct-constrain-items signature owner pending wrld)))
            (and (equal (car line) "constrain")
                 (faithful-constraint-data-p (cadr line) wrld)))
   :hints (("Goal"
            :in-theory (e/d (faithful-direct-constrain-items faithful-constraint-data-p
                             faithful-constraint-record-p
                             faithful-constraint-owner faithful-stored-constraint
                             faithful-constraint-siblings set-equiv)
                            (faithful-formula-pending bx-formula-cands bx-later-items
                             bx-sort-by-event bx-arities bx-name-formulas
                             bx-candidate-formulas constraint-info fgetprop
                             faithful-arities-p faithful-constraint-members-p
                             faithful-bx-sort-names plist-worldp-with-formals))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-record-of-constraint-landmark
   (implies (and (faithful-constraint-events-p triples wrld)
                 (faithful-event-landmark-p event triples)
                 (eq (access-event-tuple-type event) 'encapsulate))
            (faithful-constraint-landmark-data-p event wrld))
   :hints (("Goal" :induct (faithful-constraint-events-p triples wrld)
            :in-theory (e/d (faithful-event-landmark-p)
                            (access-event-tuple-type faithful-event-names))))))

(local
 (defthm faithful-name-list-of-encapsulate
   (implies (consp (access-event-tuple-namex event))
            (equal (faithful-event-names event)
                   (access-event-tuple-namex event)))
   :hints (("Goal" :in-theory (disable access-event-tuple-namex)))))

(defthm faithful-constraint-items-of-event
  (implies (and (equal (car line) "constrain")
                (faithful-constraint-world-p wrld)
                (faithful-event-landmark-p ev wrld)
                (member-equal (cons :stmt line)
                              (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                         translations wrld))))
           (let* ((signature (faithful-event-names ev))
                  (owner (faithful-constraint-owner (car signature) wrld)))
             (and (consp signature)
                  (faithful-constraint-record-p signature wrld)
                  (member-equal (cons :stmt line)
                                (faithful-direct-constrain-items signature owner pending wrld)))))
  :hints (("Goal"
           :use (faithful-statement-word-of-event
                 (:instance faithful-event-type-reader (event ev))
                 (:instance faithful-event-namex-reader (event ev))
                 (:instance faithful-event-name-reader (event ev))
                 (:instance faithful-record-of-constraint-landmark
                            (event ev) (triples wrld)))
           :in-theory (e/d (faithful-direct-event-result faithful-constraint-world-p faithful-constraint-owner
                            faithful-constraint-landmark-data-p)
                           (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                            access-event-tuple-type access-event-tuple-namex
                            faithful-event-names
                            bx-names bx-programp bx-all-program-p
                            bx-some-program-p bx-constrained-p
                            bx-all-constrained-p bx-some-constrained-p
                            bx-program-defs bx-define-items bx-add-candidates
                            bx-stobj-items fgetprop bx-conjuncts
                            bx-mentions-some constraint-info bx-choose-items
                            bx-constrain-items bx-package-items
                            bx-reserve-items bx-names-with-content
                            faithful-constraint-events-p
                            faithful-record-of-constraint-landmark))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm faithful-constraint-data-of-event
   (implies (and (equal (car line) "constrain")
                 (plist-worldp-with-formals wrld)
                 (faithful-constraint-world-p wrld)
                 (faithful-event-landmark-p ev wrld)
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                          translations wrld))))
            (faithful-constraint-data-p (cadr line) wrld))
   :hints (("Goal"
            :use (faithful-constraint-items-of-event
                  (:instance faithful-constraint-data-of-items
                             (signature (faithful-event-names ev))
                             (owner (faithful-constraint-owner
                                     (car (faithful-event-names ev)) wrld))))
            :in-theory (disable bx-event-items bx-constrain-items
                                faithful-event-names plist-worldp-with-formals)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-constraint-data-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (equal (car line) "constrain")
                   (plist-worldp-with-formals wrld)
                   (faithful-constraint-world-p wrld)
                   origin)
              (faithful-constraint-data-p (cadr line) wrld)))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  faithful-landmark-of-statement-origin
                  (:instance faithful-constraint-data-of-event
                             (ev (car (faithful-statement-origin
                                       line lo hi translations wrld)))
                             (encl (cadr (faithful-statement-origin
                                         line lo hi translations wrld)))
                             (pending (caddr (faithful-statement-origin
                                             line lo hi translations wrld)))
                             (defined (cadddr (faithful-statement-origin
                                               line lo hi translations wrld)))))
            :in-theory (disable bx-event-items plist-worldp-with-formals)
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-constrain-statement
  (implies
   (and (equal (car line) "constrain")
        (plist-worldp-with-formals wrld)
        (faithful-constraint-world-p wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-constraint-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-constraint-data-of-origin (lo 0))
                 faithful-constraint-data-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

; A constraint has a single result at the naming step. A missing label
; calls for a note identifying the functions and each available label.

(defund faithful-constraint-statement-for-p (line owner wrld)
  (and (equal (car line) "constrain")
       (equal (faithful-constraint-owner (caaar (cadr line)) wrld) owner)
       (faithful-constraint-data-p (cadr line) wrld)))

(defund faithful-missing-label-note-covers-p (line names)
  (case-match line
    (("note" ("constraint with a formula for which no unused name was found" reported))
     (subsetp-equal names reported))
    (& nil)))

(defund faithful-constraint-missing-name-note-for-p (line owner wrld)
  (faithful-missing-label-note-covers-p line (faithful-constraint-siblings owner wrld)))

(defund faithful-constraint-note-names (fns formulas)
  (append fns (remove-equal nil (strip-cars formulas))))

(defthm faithful-constraint-naming-outcome
  (let ((items (bx-constrain-stmt fns formulas wrld)))
    (if (member-equal nil (strip-cars formulas))
        (equal items
               (list (list :note "constraint with a formula for which no unused name was found"
                           (faithful-constraint-note-names fns formulas))))
      (equal items (list (list :stmt "constrain" (list (bx-arities fns wrld) formulas))))))
  :hints (("Goal" :in-theory (enable faithful-constraint-note-names)))
  :rule-classes nil)

; The naming result is the last item produced directly by the event.
; Earlier items can give further details about its formulas.

(defund faithful-constraint-report-item (signature owner pending wrld)
  (car (last (faithful-direct-constrain-items signature owner pending wrld))))

; Recover the pairs supplied to the naming outcome at this point in
; the event walk.

(defund faithful-constraint-report-formulas (owner pending wrld)
  (let ((stored (faithful-stored-constraint owner wrld))
        (candidates (bx-formula-cands (cdr (assoc-equal owner pending)))))
    (if (unknown-constraints-p stored)
        (bx-candidate-formulas candidates wrld)
      (mv-let (formulas notes)
        (bx-name-formulas stored candidates owner wrld)
        (declare (ignore notes))
        formulas))))

(local
 (defthm faithful-last-of-append-with-tail
   (implies (consp tail)
            (equal (last (append xs tail)) (last tail)))
   :hints (("Goal" :induct (append xs tail)))))

(local
 (defthm faithful-first-function-of-arity-list
   (equal (caar (bx-arities names wrld)) (car names))
   :hints (("Goal" :in-theory (disable formals)))))

(local
 (defthm faithful-subset-kept-by-appending
   (implies (subsetp-equal names prefix)
            (subsetp-equal names (append prefix suffix)))
   :hints (("Goal" :induct (len names)))))

(local
 (defthm faithful-constraint-report-is-in-direct-items
   (member-equal (faithful-constraint-report-item signature owner pending wrld)
                 (faithful-direct-constrain-items signature owner pending wrld))
   :hints (("Goal"
            :in-theory (e/d (faithful-constraint-report-item faithful-direct-constrain-items)
                            (faithful-formula-pending bx-formula-cands bx-later-items
                             bx-sort-by-event bx-arities bx-name-formulas
                             bx-candidate-formulas constraint-info fgetprop))
            :do-not-induct t))))

(local
 (defthm faithful-constraint-report-shape
   (let ((item (faithful-constraint-report-item signature owner pending wrld)))
     (implies (and (consp signature)
                   (equal owner (faithful-constraint-owner (car signature) wrld))
                   (faithful-constraint-record-p signature wrld))
              (or (and (eq (car item) :stmt)
                       (equal (cadr item) "constrain")
                       (equal (faithful-constraint-owner (caaar (caddr item)) wrld)
                              owner))
                  (and (eq (car item) :note)
                       (faithful-constraint-missing-name-note-for-p
                        (list "note" (cdr item)) owner wrld)))))
   :hints (("Goal"
            :use ((:instance faithful-members-of-bx-sibling-names
                             (siblings (faithful-constraint-siblings owner wrld))))
            :in-theory (e/d (faithful-constraint-report-item
                             faithful-constraint-missing-name-note-for-p
                             faithful-missing-label-note-covers-p
                             faithful-direct-constrain-items faithful-constraint-record-p
                             faithful-constraint-siblings set-equiv)
                            (faithful-formula-pending bx-formula-cands bx-later-items
                             bx-sort-by-event bx-arities bx-name-formulas
                             bx-candidate-formulas constraint-info fgetprop
                             faithful-constraint-members-p faithful-bx-sort-names
                             binary-append associativity-of-append))
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-exhausted-constraint-report
  (let* ((formulas (faithful-constraint-report-formulas owner pending wrld))
         (item (faithful-constraint-report-item signature owner pending wrld))
         (names (faithful-constraint-note-names
                 (faithful-constraint-siblings owner wrld) formulas)))
    (implies (and (consp signature)
                  (equal owner (faithful-constraint-owner (car signature) wrld))
                  (faithful-constraint-record-p signature wrld)
                  (member-equal nil (strip-cars formulas)))
             (and (equal item (list :note (cadr item) (caddr item)))
                  (faithful-missing-label-note-covers-p
                   (list "note" (cdr item)) names))))
  :hints (("Goal"
           :use ((:instance faithful-members-of-bx-sibling-names
                            (siblings (faithful-constraint-siblings owner wrld))))
           :in-theory (e/d (faithful-constraint-report-item
                            faithful-direct-constrain-items faithful-constraint-record-p
                            faithful-constraint-siblings faithful-stored-constraint
                            faithful-constraint-report-formulas
                            faithful-constraint-note-names faithful-missing-label-note-covers-p
                            set-equiv)
                           (faithful-formula-pending bx-formula-cands bx-later-items
                            bx-sort-by-event bx-arities bx-name-formulas
                            bx-candidate-formulas constraint-info fgetprop
                            faithful-constraint-members-p faithful-bx-sort-names
                            binary-append associativity-of-append))
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-constraint-record-of-event
  (implies (and (faithful-event-landmark-p ev wrld)
                (eq (access-event-tuple-type ev) 'encapsulate)
                (consp (faithful-event-names ev))
                (faithful-constraint-world-p wrld))
           (faithful-constraint-record-p (faithful-event-names ev) wrld))
  :hints (("Goal"
           :use ((:instance faithful-record-of-constraint-landmark
                            (event ev) (triples wrld)))
           :in-theory (e/d (faithful-constraint-world-p faithful-constraint-landmark-data-p)
                           (faithful-constraint-events-p faithful-event-names
                            access-event-tuple-type faithful-record-of-constraint-landmark))
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-constraint-report-of-landmark
  (let* ((signature (faithful-event-names ev))
         (owner (faithful-constraint-owner (car signature) wrld))
         (item (faithful-constraint-report-item signature owner pending wrld)))
    (implies (and (faithful-event-landmark-p ev wrld)
                  (eq (access-event-tuple-type ev) 'encapsulate)
                  (consp signature)
                  (faithful-constraint-world-p wrld)
                  (plist-worldp-with-formals wrld))
             (and (member-equal item
                                (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                                 translations wrld)))
                  (or (and (eq (car item) :stmt)
                           (faithful-constraint-statement-for-p (cdr item) owner wrld))
                      (and (eq (car item) :note)
                           (faithful-constraint-missing-name-note-for-p
                            (list "note" (cdr item)) owner wrld))))))
  :hints (("Goal"
           :use ((:instance faithful-event-type-reader (event ev))
                 (:instance faithful-event-namex-reader (event ev))
                 (:instance faithful-event-name-reader (event ev))
                 (:instance faithful-record-of-constraint-landmark
                            (event ev) (triples wrld))
                 (:instance faithful-constraint-report-shape
                            (signature (faithful-event-names ev))
                            (owner (faithful-constraint-owner
                                    (car (faithful-event-names ev)) wrld)))
                 (:instance cons-car-cdr
                            (x (faithful-constraint-report-item
                                (faithful-event-names ev)
                                (faithful-constraint-owner
                                 (car (faithful-event-names ev)) wrld)
                                pending wrld)))
                 (:instance faithful-constraint-data-of-items
                            (signature (faithful-event-names ev))
                            (owner (faithful-constraint-owner
                                    (car (faithful-event-names ev)) wrld))
                            (line (cdr (faithful-constraint-report-item
                                        (faithful-event-names ev)
                                        (faithful-constraint-owner
                                         (car (faithful-event-names ev)) wrld)
                                        pending wrld)))))
           :in-theory (e/d (faithful-direct-event-result faithful-constraint-world-p
                            faithful-constraint-owner faithful-constraint-landmark-data-p
                            faithful-constraint-statement-for-p)
                           (bx-event-items bx-constrain-items constraint-info
                            bx-ev-type bx-ev-namex bx-names member-equal
                            access-event-tuple-type access-event-tuple-namex
                            faithful-event-names faithful-constraint-events-p
                            faithful-record-of-constraint-landmark plist-worldp-with-formals))
           :do-not-induct t))
  :rule-classes nil)
