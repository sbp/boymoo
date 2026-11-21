(in-package "ACL2")

(include-book "structure-held-items")

; A name of an unexpected event kind needs coverage when it has logic
; content or uses the reserved-name namespace.

(defun structure-has-logical-name-p (names wrld)
  (and (consp names)
       (or (structure-logic-name-p (car names) wrld)
           (structure-has-logical-name-p (cdr names) wrld))))

(defun structure-has-reserved-name-p (names wrld)
  (and (consp names)
       (or (structure-reserved-name-p (car names) wrld)
           (structure-has-reserved-name-p (cdr names) wrld))))

(local (in-theory (disable structure-event-kind structure-event-namex
                           structure-event-class structure-event-depth
                           structure-constraint-root constraint-info)))

; Relate the world properties in the coverage alternatives to section 5.
; Note that an explicit NIL is a name of a defconst, but an absent namex
; on a form that could not introduce NIL is an empty list.

(defthm structure-nonempty-event-names
  (implies (consp (structure-event-names record))
           (equal (bx-names (structure-event-namex record))
                  (structure-event-names record))))

(defthm structure-event-name-list-agrees
  (implies (member-equal name (structure-event-names record))
           (equal (bx-names (structure-event-namex record))
                  (structure-event-names record)))
  :hints (("Goal" :cases ((consp (structure-event-names record)))
                  :in-theory (disable structure-event-names bx-names))))

(defthm structure-member-is-symbol
  (implies (and (symbol-listp names) (member-equal name names))
           (symbolp name))
  :rule-classes (:rewrite :forward-chaining))

(defthm structure-name-type-for-event
  (implies (and (structure-namex-shapep record)
                (structure-event-kind-with-statements-p (structure-event-kind record))
                (member-equal name (structure-event-names record)))
           (equal (stringp name) (eq (structure-event-kind record) 'defpkg))))

(defthm structure-logical-name-implies-logical-names
  (implies (and (member-equal name names)
                (structure-logic-name-p name wrld))
           (structure-has-logical-name-p names wrld))
  :hints (("Goal" :in-theory (disable structure-logic-name-p))))

(defthm structure-names-with-content
  (iff (bx-names-with-content names wrld)
       (structure-has-logical-name-p names wrld))
  :hints (("Goal" :in-theory (disable fgetprop))))

(defthm structure-reserved-name-implies-reserved-names
  (implies (and (member-equal name names)
                (structure-reserved-name-p name wrld))
           (structure-has-reserved-name-p names wrld))
  :hints (("Goal" :in-theory (disable structure-reserved-name-p))))

(defthm structure-names-with-reservations
  (iff (bx-names-reserved names wrld)
       (structure-has-reserved-name-p names wrld))
  :hints (("Goal" :in-theory (disable fgetprop))))

(defthm structure-constraint-lists-all-subset-names
  (implies (and (subsetp-equal names siblings) (member-equal name names))
           (member-equal name siblings)))

(defthm structure-adding-formula-keeps-its-name
  (member-equal name
                (strip-cars
                 (bx-formula-cands
                  (cdr (assoc-eq root
                                 (bx-add-candidates root (list (list name :formula formula))
                                                    pending))))))
  :hints (("Goal" :in-theory (disable bx-add-candidates append))))

(defthm structure-defthm-event-name-is-nonnil
  (implies (and (eq (structure-event-kind record) 'defthm)
                (structure-namex-shapep record)
                (member-equal name (structure-event-names record)))
           name)
  :hints (("Goal" :in-theory (disable structure-event-kind structure-event-namex)))
  :rule-classes nil)

; The current event accounts for its name now, finds a function already
; defined, or defers a sibling function or formula to a closing record.

(defthm structure-current-event-coverage
  (implies
   (and (structure-namex-shapep record)
        (member-equal name (structure-event-names record))
        (not (structure-no-statement-due-p name record wrld)))
   (let* ((kind (structure-event-kind record))
          (result (bx-event-items record enclosing pending defined translations wrld)))
     (or (structure-items-account-for-p name (car result))
         (and (not (stringp name))
              (or (and (member-eq kind '(defstobj defabsstobj))
                       (hons-get name defined))
                  (and enclosing (member-equal name (getpropc enclosing 'siblings nil wrld)))
                  (and name enclosing (eq kind 'defthm)
                       (member-equal name
                                     (strip-cars (bx-formula-cands
                                                  (cdr (assoc-eq enclosing
                                                                 (mv-nth 1 result))))))))))))
  :hints
  (("Goal"
    :use ((:instance structure-name-type-for-event)
          (:instance structure-single-event-name)
          (:instance structure-defthm-event-name-is-nonnil)
          (:instance structure-event-name-list-agrees)
          (:instance structure-logical-name-implies-logical-names
                     (names (structure-event-names record)))
          (:instance structure-reserved-name-implies-reserved-names
                     (names (structure-event-names record))))
    :in-theory
    (disable bx-ev-form bx-ev-type bx-ev-namex bx-ev-symbol-class bx-names
             bx-add-candidates bx-program-defs bx-define-items bx-stobj-items
             bx-choose-items bx-all-program-p bx-all-constrained-p bx-some-constrained-p
             bx-some-program-p bx-definition-candidates bx-mentions-some bx-conjuncts
             bx-constrain-items bx-constrainer bx-formula-name bx-constrained-p
             bx-reserve-items bx-package-items bx-names-with-content bx-names-reserved
             bx-formula-cands structure-pending-entry-after-add subsetp-equal
             fgetprop structure-items-account-for-p structure-coverage-is-statement-or-note
             structure-event-names structure-namex-shapep
             structure-has-logical-name-p structure-logic-name-p
             structure-has-reserved-name-p structure-reserved-name-p))))

; Each entry in DEFINED is backed by a statement in the accumulator or
; in a bundle awaiting its closing event.

(defthm structure-name-installed-by-add-names
  (iff (hons-get name (bx-add-names new defined))
       (or (member-equal name new) (hons-get name defined)))
  :hints (("Goal" :induct (bx-add-names new defined)
                  :in-theory (enable bx-add-names hons-get hons-acons))))

(defthm structure-introduced-member-is-covered
  (implies (and (not (stringp name))
                (member-equal name (bx-introduced line)))
           (structure-event-line-supplies-p name line))
  :hints (("Goal" :in-theory (enable bx-introduced))))

(defthm structure-added-definition-is-covered
  (implies (and (not (stringp name))
                (hons-get name (bx-add-defined items defined)))
           (or (hons-get name defined)
               (structure-items-account-for-p name items)))
  :hints (("Goal" :induct (bx-add-defined items defined)
                  :in-theory (disable bx-add-names bx-introduced hons-get
                                      structure-line-supplies-p
                                      structure-coverage-is-statement-or-note))))

(defun structure-accounting-item (name items)
  (cond ((endp items) nil)
        ((structure-item-accounts-for-p name (car items)) (car items))
        (t (structure-accounting-item name (cdr items)))))

(defthm structure-accounting-item-is-a-witness
  (implies (structure-items-account-for-p name items)
           (let ((item (structure-accounting-item name items)))
             (and (member-equal item items)
                  (structure-item-accounts-for-p name item))))
  :hints (("Goal" :induct (structure-accounting-item name items)
                  :in-theory (disable structure-item-accounts-for-p
                                      structure-coverage-is-statement-or-note))))

(defthm structure-accounted-for-by-member
  (implies (and (member-equal item items) (structure-item-accounts-for-p name item))
           (structure-items-account-for-p name items))
  :hints (("Goal" :induct (member-equal item items)
                  :in-theory (disable structure-item-accounts-for-p
                                      structure-coverage-is-statement-or-note)))
  :rule-classes nil)

(local (in-theory (disable bx-items bx-event-items bx-add-defined bx-add-candidates
                           bx-names bx-constrain-items bx-constrainer bx-ev-type bx-ev-namex
                           hons-get revappend reverse structure-defer-items-p
                           structure-live-held-items structure-accounting-item
                           structure-items-account-for-p structure-item-accounts-for-p
                           structure-coverage-is-statement-or-note)))

(defun structure-live-coverage-p (name pairs pending wrld acc)
  (structure-items-account-for-p name
                                (append acc (structure-live-held-items pairs pending wrld))))

(defthm structure-live-coverage-survives
  (implies (and (structure-closed-pairs-p pairs wrld)
                (structure-live-coverage-p name pairs pending wrld acc))
           (structure-items-account-for-p name (bx-items pairs pending defined translations wrld acc)))
  :hints (("Goal"
           :use ((:instance structure-accounting-item-is-a-witness
                            (items (append acc (structure-live-held-items pairs pending wrld))))
                 (:instance structure-live-items-survive
                            (item (structure-accounting-item
                                   name (append acc (structure-live-held-items pairs pending wrld)))))
                 (:instance structure-accounted-for-by-member
                            (item (structure-accounting-item
                                   name (append acc (structure-live-held-items pairs pending wrld))))
                            (items (bx-items pairs pending defined translations wrld acc))))
           :in-theory (disable structure-item-coverage-of-append
                               structure-accounting-item-is-a-witness
                               structure-live-items-survive append))))

(defthm structure-current-event-coverage-survives
  (let ((items (car (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld))))
    (implies (and (consp pairs)
                  (structure-closed-pairs-p pairs wrld)
                  (structure-items-account-for-p name items))
             (structure-items-account-for-p name
                                            (bx-items pairs pending defined translations wrld acc))))
  :hints (("Goal"
           :use ((:instance structure-accounting-item-is-a-witness
                            (items (car (bx-event-items (caar pairs) (cdar pairs) pending defined
                                                       translations wrld))))
                 (:instance structure-current-event-items-survive
                            (item (structure-accounting-item
                                   name (car (bx-event-items (caar pairs) (cdar pairs) pending
                                                             defined translations wrld)))))
                 (:instance structure-accounted-for-by-member
                            (item (structure-accounting-item
                                   name (car (bx-event-items (caar pairs) (cdar pairs) pending
                                                             defined translations wrld))))
                            (items (bx-items pairs pending defined translations wrld acc))))
           :in-theory (disable structure-current-event-items-survive
                               structure-accounting-item-is-a-witness))))

(defthm structure-witness-still-accounts-for-name
  (implies (and (member-equal (structure-accounting-item name before) items)
                (structure-item-accounts-for-p name (structure-accounting-item name before)))
           (structure-items-account-for-p name items))
  :hints (("Goal" :use ((:instance structure-accounted-for-by-member
                                   (item (structure-accounting-item name before))))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((member-equal (structure-accounting-item name before) items)))))

; The coverage invariant is membership of a concrete accounting item
; in the accumulator or a live bundle.

(defthm structure-step-keeps-live-coverage
  (let* ((result (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld))
         (items (car result))
         (pending1 (mv-nth 1 result))
         (enclosing (cdar pairs))
         (defer (structure-defer-items-p items enclosing pending1 wrld)))
    (implies (and (consp pairs)
                  (structure-closed-pairs-p pairs wrld)
                  (or (structure-live-coverage-p name pairs pending wrld acc)
                      (structure-items-account-for-p name items)))
             (structure-live-coverage-p
              name (cdr pairs)
              (if defer (bx-add-candidates enclosing (list (list nil :after items)) pending1)
                pending1)
              wrld (if defer acc (revappend items acc)))))
  :hints
  (("Goal"
    :use ((:instance structure-accounting-item-is-a-witness
                     (items (append
                             (car (bx-event-items (caar pairs) (cdar pairs) pending defined
                                                  translations wrld))
                             acc (structure-live-held-items pairs pending wrld))))
          (:instance structure-step-keeps-live-item
                     (item (structure-accounting-item
                            name (append
                                  (car (bx-event-items (caar pairs) (cdar pairs) pending defined
                                                       translations wrld))
                                  acc (structure-live-held-items pairs pending wrld))))))
    :in-theory (disable structure-accounting-item-is-a-witness
                        structure-step-keeps-live-item structure-live-items-after-event
                        structure-live-items-after-holding structure-member-of-revappend
                        structure-item-coverage-of-revappend append))))

; A signed encapsulate accounts for its siblings and the names of its
; formula candidates.

(defthm structure-closing-record-accounts-for-sibling
  (implies (and (not (stringp name))
                (structure-root-closes-p root record wrld)
                (member-equal name (getpropc root 'siblings nil wrld)))
           (structure-items-account-for-p
            name (car (bx-event-items record enclosing pending defined translations wrld))))
  :hints (("Goal"
           :expand ((bx-event-items record enclosing pending defined translations wrld))
           :in-theory (enable bx-names))))

(defthm structure-closing-record-accounts-for-candidate
  (implies (and name
                (not (stringp name))
                (structure-root-closes-p root record wrld)
                (member-equal name (strip-cars (bx-formula-cands
                                                (cdr (assoc-eq root pending))))))
           (structure-items-account-for-p
            name (car (bx-event-items record enclosing pending defined translations wrld))))
  :hints (("Goal"
           :expand ((bx-event-items record enclosing pending defined translations wrld))
           :use ((:instance structure-constrain-items-account-for-formula
                            (names (structure-event-namex record))))
           :in-theory (e/d (bx-names)
                           (bx-formula-cands fgetprop
                            structure-constrain-items-account-for-formula)))))

(defthm structure-carrier-accounts-for-sibling
  (implies (and (not (stringp name))
                (member-equal name (getpropc root 'siblings nil wrld))
                (structure-carrier-present-p root pairs wrld)
                (structure-closed-pairs-p pairs wrld))
           (structure-items-account-for-p
            name (bx-items pairs pending defined translations wrld acc)))
  :hints (("Goal" :induct (structure-delivery-induction pairs pending defined translations wrld acc)
                  :in-theory (disable fgetprop structure-root-closes-p))
          ("Subgoal *1/3" :cases ((structure-root-closes-p root (caar pairs) wrld)))
          ("Subgoal *1/2" :cases ((structure-root-closes-p root (caar pairs) wrld)))
          ("Subgoal *1/3.1"
           :use ((:instance structure-closing-record-accounts-for-sibling
                            (record (caar pairs)) (enclosing (cdar pairs))))
           :in-theory (disable structure-items-step))
          ("Subgoal *1/2.1"
           :use ((:instance structure-closing-record-accounts-for-sibling
                            (record (caar pairs)) (enclosing (cdar pairs))))
           :in-theory (disable structure-items-step))))

(defthm structure-carrier-accounts-for-candidate
  (implies (and name
                (not (stringp name))
                (member-equal name (strip-cars (bx-formula-cands
                                                (cdr (assoc-eq root pending)))))
                (structure-carrier-present-p root pairs wrld)
                (structure-closed-pairs-p pairs wrld))
           (structure-items-account-for-p
            name (bx-items pairs pending defined translations wrld acc)))
  :hints (("Goal" :induct (structure-delivery-induction pairs pending defined translations wrld acc)
                  :in-theory (disable structure-root-closes-p bx-formula-cands
                                      structure-pending-entry-after-add))
          ("Subgoal *1/3" :cases ((structure-root-closes-p root (caar pairs) wrld)))
          ("Subgoal *1/2" :cases ((structure-root-closes-p root (caar pairs) wrld)))
          ("Subgoal *1/3.1"
           :use ((:instance structure-closing-record-accounts-for-candidate
                            (record (caar pairs)) (enclosing (cdar pairs))))
           :in-theory (disable structure-items-step))
          ("Subgoal *1/2.1"
           :use ((:instance structure-closing-record-accounts-for-candidate
                            (record (caar pairs)) (enclosing (cdar pairs))))
           :in-theory (disable structure-items-step))))

(defthm structure-carrier-in-tail-is-present
  (implies (and (consp pairs)
                (structure-carrier-present-p root (cdr pairs) wrld))
           (structure-carrier-present-p root pairs wrld))
  :hints (("Goal" :in-theory (disable structure-root-closes-p))))

(defthm structure-current-candidate-carried
  (let* ((root (cdar pairs))
         (pending1 (mv-nth 1 (bx-event-items (caar pairs) root pending defined translations wrld)))
         (items (bx-items pairs pending defined translations wrld acc)))
    (implies (and (consp pairs)
                  root
                  name
                  (not (stringp name))
                  (structure-closed-pairs-p pairs wrld)
                  (member-equal name (strip-cars (bx-formula-cands
                                                  (cdr (assoc-eq root pending1))))))
             (structure-items-account-for-p name items)))
  :hints (("Goal"
           :use ((:instance structure-carrier-accounts-for-candidate
                            (root (cdar pairs)) (pairs (cdr pairs))
                            (pending
                             (let* ((event (bx-event-items
                                            (caar pairs) (cdar pairs) pending defined
                                            translations wrld))
                                    (items (car event))
                                    (pending1 (mv-nth 1 event)))
                               (if (structure-defer-items-p items (cdar pairs) pending1 wrld)
                                   (bx-add-candidates (cdar pairs)
                                                      (list (list nil :after items)) pending1)
                                 pending1)))
                            (defined
                             (bx-add-defined
                              (car (bx-event-items (caar pairs) (cdar pairs) pending defined
                                                   translations wrld))
                              defined))
                            (acc
                             (let* ((event (bx-event-items
                                            (caar pairs) (cdar pairs) pending defined
                                            translations wrld))
                                    (items (car event))
                                    (pending1 (mv-nth 1 event)))
                               (if (structure-defer-items-p items (cdar pairs) pending1 wrld)
                                   acc
                                 (revappend items acc))))))
           :in-theory (disable structure-carrier-present-p
                               structure-carrier-accounts-for-candidate
                               bx-formula-cands
                               structure-pending-entry-after-add))))

; Each selected record can be accounted for when its head or some
; later closing record is processed.

(defthm structure-covered-definition-in-next-step
  (let* ((result (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld))
         (items (car result))
         (pending1 (mv-nth 1 result))
         (enclosing (cdar pairs))
         (defer (structure-defer-items-p items enclosing pending1 wrld)))
    (implies (and (consp pairs)
                  (structure-closed-pairs-p pairs wrld)
                  (not (stringp name))
                  (or (not (hons-get name defined))
                      (structure-live-coverage-p name pairs pending wrld acc))
                  (hons-get name (bx-add-defined items defined)))
             (structure-live-coverage-p
              name (cdr pairs)
              (if defer (bx-add-candidates enclosing (list (list nil :after items)) pending1)
                pending1)
              wrld (if defer acc (revappend items acc)))))
  :hints (("Goal"
           :use ((:instance structure-added-definition-is-covered
                            (items (car (bx-event-items (caar pairs) (cdar pairs) pending defined
                                                       translations wrld))))
                 (:instance structure-step-keeps-live-coverage))
           :in-theory (disable structure-live-coverage-p
                               structure-added-definition-is-covered
                               structure-step-keeps-live-coverage))))

(defthm structure-current-record-covered
  (implies
   (and (consp pairs)
        (structure-namex-shapep (caar pairs))
        (member-equal name (structure-event-names (caar pairs)))
        (not (structure-no-statement-due-p name (caar pairs) wrld))
        (structure-closed-pairs-p pairs wrld)
        (or (stringp name)
            (not (hons-get name defined))
            (structure-live-coverage-p name pairs pending wrld acc)))
   (structure-items-account-for-p name (bx-items pairs pending defined translations wrld acc)))
  :hints
  (("Goal"
    :use ((:instance structure-current-event-coverage
                     (record (caar pairs)) (enclosing (cdar pairs)))
          (:instance structure-live-coverage-survives)
          (:instance structure-current-event-coverage-survives)
          (:instance structure-carrier-accounts-for-sibling (root (cdar pairs)))
          (:instance structure-carrier-in-tail-is-present (root (cdar pairs)))
          (:instance structure-current-candidate-carried))
    :in-theory (disable structure-no-statement-due-p structure-namex-shapep
                        structure-event-names structure-carrier-present-p
                        structure-live-coverage-p
                        structure-current-event-coverage structure-live-coverage-survives
                        structure-current-candidate-carried
                        structure-carrier-in-tail-is-present
                        structure-items-step bx-formula-cands
                        structure-pending-entry-after-add))))

(defthm structure-closed-pairs-tail
  (implies (structure-closed-pairs-p pairs wrld)
           (structure-closed-pairs-p (cdr pairs) wrld)))

(defthm structure-items-cover-range-name
  (implies
   (and (member-equal record (strip-cars pairs))
        (structure-namex-shapep record)
        (member-equal name (structure-event-names record))
        (not (structure-no-statement-due-p name record wrld))
        (structure-closed-pairs-p pairs wrld)
        (or (stringp name)
            (not (hons-get name defined))
            (structure-live-coverage-p name pairs pending wrld acc)))
   (structure-items-account-for-p name (bx-items pairs pending defined translations wrld acc)))
  :hints
  (("Goal" :induct (structure-delivery-induction pairs pending defined translations wrld acc)
           :in-theory (disable structure-no-statement-due-p structure-namex-shapep
                               structure-event-names structure-carrier-present-p
                               structure-live-coverage-p
                               structure-closed-pairs-p structure-items-step
                               structure-current-record-covered
                               structure-covered-definition-in-next-step))
   ("Subgoal *1/3" :cases ((equal record (caar pairs))))
   ("Subgoal *1/2" :cases ((equal record (caar pairs))))
   ("Subgoal *1/3.1" :use ((:instance structure-current-record-covered)))
   ("Subgoal *1/2.1" :use ((:instance structure-current-record-covered)))
   ("Subgoal *1/3.2" :use ((:instance structure-covered-definition-in-next-step)
                          (:instance structure-items-step)))
   ("Subgoal *1/2.2" :use ((:instance structure-covered-definition-in-next-step)
                          (:instance structure-items-step)))))
