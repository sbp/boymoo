(in-package "ACL2")

(include-book "structure-items")
(include-book "structure-enclosure")

; A future pair carries its record and the name of its enclosing
; constraint.  The closing record supplies a root of its own.

(defun structure-root-closes-p (root record wrld)
  (and (eq (structure-event-kind record) 'encapsulate)
       (consp (structure-event-namex record))
       (equal (structure-constraint-root record wrld) root)))

(defun structure-carrier-present-p (root later wrld)
  (and (consp later)
       (or (structure-root-closes-p root (caar later) wrld)
           (structure-carrier-present-p root (cdr later) wrld))))

; No theorem needs to assume that there is a closing event for a recorded
; enclosing root.  The root is obtained from the later landmarks.

(defun structure-root-among-records-p (root records wrld)
  (and (consp records)
       (or (structure-root-closes-p root (car records) wrld)
           (structure-root-among-records-p root (cdr records) wrld))))

(defun structure-closed-pairs-p (pairs wrld)
  (or (endp pairs)
      (and (or (not (cdar pairs))
               (structure-carrier-present-p (cdar pairs) (cdr pairs) wrld))
           (structure-closed-pairs-p (cdr pairs) wrld))))

(local (in-theory (disable structure-event-kind structure-event-namex
                           structure-event-class structure-event-depth
                           structure-constraint-root constraint-info)))

(defthm structure-nearest-root-is-among-ancestors
  (implies (structure-nearest-root ancestors wrld)
           (structure-root-among-records-p (structure-nearest-root ancestors wrld)
                                           ancestors wrld))
  :hints (("Goal" :induct (structure-nearest-root ancestors wrld))
          ("Subgoal *1/2"
           :expand ((structure-constraint-root (car ancestors) wrld)))))

(defthm structure-ancestors-are-from-later-records
  (implies (structure-root-among-records-p root (structure-enclosing-landmarks later depth) wrld)
           (structure-root-among-records-p root later wrld))
  :hints (("Goal" :induct (structure-enclosing-landmarks later depth))))

(defthm structure-root-in-pairs
  (iff (structure-root-among-records-p root (strip-cars pairs) wrld)
       (structure-carrier-present-p root pairs wrld)))

(defthm structure-nearest-root-has-carrier
  (let ((ancestors (structure-enclosing-landmarks (strip-cars pairs) depth)))
    (implies (structure-nearest-root ancestors wrld)
             (structure-carrier-present-p (structure-nearest-root ancestors wrld)
                                          pairs wrld)))
  :hints (("Goal"
           :use ((:instance structure-nearest-root-is-among-ancestors
                            (ancestors (structure-enclosing-landmarks (strip-cars pairs) depth)))
                 (:instance structure-ancestors-are-from-later-records
                            (later (strip-cars pairs))
                            (root (structure-nearest-root
                                   (structure-enclosing-landmarks (strip-cars pairs) depth)
                                   wrld))))
           :in-theory (disable structure-enclosing-landmarks structure-nearest-root
                               structure-carrier-present-p structure-root-among-records-p
                               structure-ancestors-are-from-later-records
                               structure-nearest-root-is-among-ancestors))))

(defthm structure-pairing-keeps-carriers
  (implies (and (structure-closed-pairs-p acc wrld)
                (equal later (strip-cars acc)))
           (structure-closed-pairs-p
            (structure-pair-range-events newest later wrld acc) wrld))
  :hints (("Goal" :induct (structure-pair-range-events newest later wrld acc)
                  :in-theory (disable structure-nearest-root structure-enclosing-landmarks
                                      structure-carrier-present-p structure-root-closes-p))))

; The two kinds of pending entries are independent.  Event conversion
; can add formula candidates.  Holding back items adds a bundle of them
; without altering the formula candidates.

(defthm structure-pending-entry-after-add
  (equal (cdr (assoc-eq root (bx-add-candidates added candidates pending)))
         (if (equal root added)
             (append (cdr (assoc-eq root pending)) candidates)
           (cdr (assoc-eq root pending))))
  :hints (("Goal" :cases ((equal root added)))))

(defthm structure-later-items-of-append
  (equal (bx-later-items (append a b))
         (append (bx-later-items a) (bx-later-items b))))

(defthm structure-formula-candidates-of-append
  (equal (bx-formula-cands (append a b))
         (append (bx-formula-cands a) (bx-formula-cands b))))

(defthm structure-later-items-form-a-list
  (true-listp (bx-later-items candidates))
  :rule-classes :type-prescription)

(defthm structure-formula-candidates-form-a-list
  (true-listp (bx-formula-cands candidates))
  :rule-classes :type-prescription)

(defthm structure-no-later-items-among-definitions
  (equal (bx-later-items (bx-definition-candidates names wrld)) nil)
  :hints (("Goal" :in-theory (disable bx-formula-name))))

(defthm structure-holding-items-keeps-formulas
  (equal (bx-formula-cands
          (cdr (assoc-eq root
                         (bx-add-candidates added (list (list nil :after items)) pending))))
         (bx-formula-cands (cdr (assoc-eq root pending))))
  :hints (("Goal" :in-theory (disable bx-add-candidates append))))

(defthm structure-held-items-after-adding-bundle
  (iff (member-equal item
                     (bx-later-items
                      (cdr (assoc-eq root
                                     (bx-add-candidates added
                                                        (list (list nil :after items))
                                                        pending)))))
       (or (member-equal item (bx-later-items (cdr (assoc-eq root pending))))
           (and (equal root added) (member-equal item items))))
  :hints (("Goal" :in-theory (disable bx-add-candidates append))))

(defthm structure-event-keeps-held-items
  (equal (bx-later-items
          (cdr (assoc-eq root (mv-nth 1
                                     (bx-event-items record enclosing pending defined
                                                     translations wrld)))))
         (bx-later-items (cdr (assoc-eq root pending))))
  :hints (("Goal"
           :in-theory (disable bx-ev-form bx-ev-type bx-ev-namex bx-ev-symbol-class
                               bx-names bx-add-candidates bx-program-defs
                               bx-define-items bx-stobj-items bx-choose-items
                               bx-all-program-p bx-all-constrained-p bx-some-constrained-p
                               bx-some-program-p bx-definition-candidates
                               bx-mentions-some bx-conjuncts bx-constrain-items
                               bx-constrainer bx-formula-name bx-constrained-p
                               bx-reserve-items bx-package-items bx-names-with-content
                               bx-names-reserved subsetp-equal fgetprop))))

(defthm structure-event-keeps-formula-candidate
  (implies (member-equal name (strip-cars (bx-formula-cands
                                         (cdr (assoc-eq root pending)))))
           (member-equal
            name
            (strip-cars (bx-formula-cands
                         (cdr (assoc-eq root (mv-nth 1
                                                    (bx-event-items record enclosing
                                                                    pending defined
                                                                    translations wrld))))))))
  :hints (("Goal"
           :in-theory (disable bx-ev-form bx-ev-type bx-ev-namex bx-ev-symbol-class
                               bx-names bx-add-candidates bx-program-defs
                               bx-define-items bx-stobj-items bx-choose-items
                               bx-all-program-p bx-all-constrained-p bx-some-constrained-p
                               bx-some-program-p bx-definition-candidates
                               bx-mentions-some bx-conjuncts bx-constrain-items
                               bx-constrainer bx-formula-name bx-constrained-p
                               bx-reserve-items bx-package-items bx-names-with-content
                               bx-names-reserved subsetp-equal fgetprop))))

; A closing event releases its bundle, even when the constraint itself
; cannot be written.  A bundle is live if there is a closing event in
; the suffix of the event sequence.

(defthm structure-constraint-releases-items
  (implies (member-equal item (bx-later-items (cdr (assoc-eq root pending))))
           (member-equal item (bx-constrain-items names root pending wrld)))
  :hints (("Goal" :in-theory (disable bx-arities bx-name-formulas bx-constrain-stmt
                                      bx-formula-cands bx-later-items constraint-info))))

(defthm structure-closing-event-releases-items
  (implies (and (structure-root-closes-p root record wrld)
                (member-equal item (bx-later-items (cdr (assoc-eq root pending)))))
           (member-equal item (car (bx-event-items record enclosing pending defined
                                                   translations wrld))))
  :hints (("Goal"
           :in-theory (disable bx-ev-type bx-ev-namex bx-constrainer bx-constrain-items
                               bx-later-items))))

(defun structure-live-held-items (pairs pending wrld)
  (if (endp pairs)
      nil
    (let* ((record (caar pairs))
           (root (structure-constraint-root record wrld)))
      (append (and (structure-root-closes-p root record wrld)
                   (bx-later-items (cdr (assoc-eq root pending))))
              (structure-live-held-items (cdr pairs) pending wrld)))))

(defthm structure-live-items-after-event
  (equal (structure-live-held-items
          pairs (mv-nth 1 (bx-event-items record enclosing pending defined translations wrld))
          wrld)
         (structure-live-held-items pairs pending wrld))
  :hints (("Goal" :in-theory (disable bx-event-items bx-later-items structure-root-closes-p))))

(defthm structure-live-items-after-holding
  (iff (member-equal item (structure-live-held-items
                           pairs (bx-add-candidates root (list (list nil :after items)) pending)
                           wrld))
       (or (member-equal item (structure-live-held-items pairs pending wrld))
           (and (structure-carrier-present-p root pairs wrld) (member-equal item items))))
  :hints (("Goal" :induct (structure-live-held-items pairs pending wrld)
                  :in-theory (disable bx-add-candidates bx-later-items
                                      structure-root-closes-p
                                      structure-pending-entry-after-add))
          ("Subgoal *1/2" :expand ((structure-root-closes-p root (caar pairs) wrld)
                                    (structure-root-closes-p
                                     (structure-constraint-root (caar pairs) wrld)
                                     (caar pairs) wrld)))))

(defthm structure-live-items-released-or-still-live
  (implies (and (consp pairs)
                (member-equal item (structure-live-held-items pairs pending wrld)))
           (or (member-equal item
                             (car (bx-event-items (caar pairs) (cdar pairs) pending defined
                                                  translations wrld)))
               (member-equal item (structure-live-held-items (cdr pairs) pending wrld))))
  :hints (("Goal"
           :use ((:instance structure-closing-event-releases-items
                            (record (caar pairs)) (enclosing (cdar pairs))
                            (root (structure-constraint-root (caar pairs) wrld))))
           :in-theory (disable bx-event-items bx-later-items structure-root-closes-p
                               structure-closing-event-releases-items))))

; BX-ITEMS either emits the current bundle or moves it to a live root.
; A bundle released by one constraint can thereby pass to an outer one.

(defun structure-defer-items-p (items enclosing pending wrld)
  (and enclosing
       (intersectp-eq (bx-items-used items)
                      (append (getpropc enclosing 'siblings nil wrld)
                              (bx-items-introduced
                               (bx-later-items (cdr (assoc-eq enclosing pending))))))))

(defthm structure-no-holding-without-an-enclosure
  (not (structure-defer-items-p items nil pending wrld)))

(defthm structure-no-live-items-without-events
  (implies (not (consp pairs))
           (equal (structure-live-held-items pairs pending wrld) nil)))

(defthm structure-items-step
  (implies (consp pairs)
           (let* ((result (bx-event-items (caar pairs) (cdar pairs) pending defined
                                          translations wrld))
                  (items (car result))
                  (pending1 (mv-nth 1 result))
                  (enclosing (cdar pairs))
                  (defer (structure-defer-items-p items enclosing pending1 wrld)))
             (equal (bx-items pairs pending defined translations wrld acc)
                    (bx-items (cdr pairs)
                              (if defer
                                  (bx-add-candidates enclosing (list (list nil :after items))
                                                     pending1)
                                pending1)
                              (bx-add-defined items defined) translations wrld
                              (if defer acc (revappend items acc))))))
  :hints (("Goal"
           :expand ((bx-items pairs pending defined translations wrld acc))
           :in-theory (disable bx-items bx-event-items bx-add-candidates bx-add-defined
                               bx-items-used bx-items-introduced bx-later-items fgetprop
                               revappend))))

(defthm structure-items-empty
  (implies (not (consp pairs))
           (equal (bx-items pairs pending defined translations wrld acc)
                  (reverse acc))))

(defthm structure-step-keeps-live-item
  (let* ((result (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld))
         (items (car result))
         (pending1 (mv-nth 1 result))
         (enclosing (cdar pairs))
         (defer (structure-defer-items-p items enclosing pending1 wrld)))
    (implies (and (consp pairs)
                  (structure-closed-pairs-p pairs wrld)
                  (or (member-equal item acc)
                      (member-equal item (structure-live-held-items pairs pending wrld))
                      (member-equal item items)))
             (or (member-equal item (if defer acc (revappend items acc)))
                 (member-equal
                  item
                  (structure-live-held-items
                   (cdr pairs)
                   (if defer
                       (bx-add-candidates enclosing (list (list nil :after items)) pending1)
                     pending1)
                   wrld)))))
  :hints (("Goal"
           :use ((:instance structure-live-items-released-or-still-live))
           :in-theory (disable bx-event-items bx-later-items bx-add-candidates
                               structure-root-closes-p structure-carrier-present-p
                               structure-live-held-items structure-defer-items-p
                               structure-live-items-released-or-still-live revappend))))

; The induction follows the delivery step.  The first head or bundle
; which holds an item may change, but every live item is eventually
; present in the result.

(defun structure-delivery-induction (pairs pending defined translations wrld acc)
  (declare (xargs :measure (acl2-count pairs)))
  (if (endp pairs)
      acc
    (mv-let (items pending1)
      (bx-event-items (caar pairs) (cdar pairs) pending defined translations wrld)
      (let* ((enclosing (cdar pairs))
             (defined1 (bx-add-defined items defined)))
        (if (structure-defer-items-p items enclosing pending1 wrld)
            (structure-delivery-induction
             (cdr pairs)
             (bx-add-candidates enclosing (list (list nil :after items)) pending1)
             defined1 translations wrld acc)
          (structure-delivery-induction (cdr pairs) pending1 defined1 translations wrld
                                        (revappend items acc)))))))

(local (in-theory (disable bx-items bx-event-items bx-add-candidates bx-add-defined
                           structure-root-closes-p structure-carrier-present-p
                           structure-live-held-items structure-defer-items-p
                           bx-later-items revappend reverse)))

(defthm structure-live-items-survive
  (implies (and (structure-closed-pairs-p pairs wrld)
                (or (member-equal item acc)
                    (member-equal item (structure-live-held-items pairs pending wrld))))
           (member-equal item (bx-items pairs pending defined translations wrld acc)))
  :hints (("Goal" :induct (structure-delivery-induction
                          pairs pending defined translations wrld acc))
          ("Subgoal *1/3" :use ((:instance structure-step-keeps-live-item)))
          ("Subgoal *1/2" :use ((:instance structure-step-keeps-live-item)))))

(defthm structure-current-event-items-survive
  (implies (and (consp pairs)
                (structure-closed-pairs-p pairs wrld)
                (member-equal item
                              (car (bx-event-items (caar pairs) (cdar pairs) pending
                                                   defined translations wrld))))
           (member-equal item (bx-items pairs pending defined translations wrld acc)))
  :hints (("Goal" :use ((:instance structure-step-keeps-live-item)))))
