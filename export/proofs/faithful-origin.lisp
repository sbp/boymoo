(in-package "ACL2")

(include-book "core")

; The library can discard or reorder statements. Each line of its result
; must still be one of the lines supplied to it.

(defthm faithful-member-of-revappend
  (iff (member-equal x (revappend a b))
       (or (member-equal x a) (member-equal x b)))
  :hints (("Goal" :induct (revappend a b)
           :in-theory (enable revappend))))

(defthm faithful-member-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b))))

(local
 (defthm faithful-member-of-reverse
   (implies (and (not (stringp a))
                 (member-equal x (reverse a)))
            (member-equal x a))
   :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm faithful-member-of-bx-words
   (implies (member-equal line (bx-words words stmts))
            (member-equal line stmts))))

(local
 (defund faithful-ground-axiom-name-p (name)
   (member-equal name *bx-ground-axioms*)))

(local
 (defthm faithful-test-of-ground-axiom-name
   (equal (member-equal name *bx-ground-axioms*)
          (faithful-ground-axiom-name-p name))
   :hints (("Goal"
            :in-theory (e/d (faithful-ground-axiom-name-p) (member-equal))))))

(defthm faithful-member-of-bx-not-ground
  (implies (member-equal line (bx-not-ground stmts ground))
           (member-equal line stmts))
  :hints (("Goal" :induct (bx-not-ground stmts ground)
           :in-theory (disable bx-introduced))))

(local
 (defthm faithful-cdr-of-hons-get-in-values
   (implies (and (hons-get key index)
                 (not (member-equal val (strip-cdrs index))))
            (not (equal (cdr (hons-get key index)) val)))
   :hints (("Goal" :in-theory (enable hons-get hons-assoc-equal)))))

(local
 (defthm faithful-values-of-bx-index-fns
   (implies (and (not (equal line stmt))
                 (not (member-equal line (strip-cdrs index))))
            (not (member-equal line
                               (strip-cdrs (bx-index-fns fns stmt index)))))
   :hints (("Goal" :in-theory (enable hons-acons)))))

(local
 (defthm faithful-values-of-bx-index
   (implies (and (not (member-equal line stmts))
                 (not (member-equal line (strip-cdrs index))))
            (not (member-equal line (strip-cdrs (bx-index stmts index)))))
   :hints (("Goal" :in-theory (disable bx-introduced)))))

(local
 (defthm faithful-member-of-bx-walk
   (implies (and (not (member-equal line (strip-cars stack)))
                 (not (member-equal line todo))
                 (not (member-equal line (strip-cdrs index)))
                 (not (member-equal line acc))
                 (not (stringp acc)))
            (not (member-equal line
                               (mv-nth 0 (bx-walk stack todo index done
                                                  acc notes fuel)))))
   :hints (("Goal"
            :induct (bx-walk stack todo index done acc notes fuel)
            :in-theory (disable bx-used bx-introduced bx-note
                                hons-get hons-acons)))))

(local
 (defthm faithful-member-of-bx-library-order
   (implies (member-equal line (mv-nth 0 (bx-library-order stmts)))
            (member-equal line stmts))
   :hints (("Goal"
            :use ((:instance faithful-member-of-bx-walk
                             (stack nil)
                             (todo (bx-words '("define" "constrain" "choose") stmts))
                             (index (bx-index
                                     (bx-words '("define" "constrain" "choose") stmts)
                                     nil))
                             (done nil) (acc nil) (notes nil)
                             (fuel (bx-steps
                                    (bx-words '("define" "constrain" "choose") stmts)))))
            :in-theory (disable bx-words bx-index bx-walk bx-steps
                                faithful-member-of-bx-walk)
            :do-not-induct t))))

(local
 (defthm faithful-member-of-ordered-not-ground
   (implies (member-equal line (car (bx-library-order (bx-not-ground stmts ground))))
            (member-equal line stmts))
   :hints (("Goal"
            :use (faithful-member-of-bx-not-ground
                  (:instance faithful-member-of-bx-library-order
                             (stmts (bx-not-ground stmts ground))))
            :in-theory (disable bx-not-ground bx-library-order
                                faithful-member-of-bx-not-ground
                                faithful-member-of-bx-library-order)))
   :rule-classes ((:forward-chaining
                   :trigger-terms
                   ((member-equal line
                                  (car (bx-library-order
                                        (bx-not-ground stmts ground)))))))))

; An encapsulate releases the items of its enclosed events as well as
; producing its own items. Keep the formula candidates when isolating
; the items produced by the current event.

(defun faithful-formula-pending (pending)
  (if (endp pending)
      nil
    (cons (cons (caar pending) (bx-formula-cands (cdar pending)))
          (faithful-formula-pending (cdr pending)))))

(defthm faithful-formulas-in-projected-pending
  (equal (cdr (assoc-equal owner (faithful-formula-pending pending)))
         (bx-formula-cands (cdr (assoc-equal owner pending))))
  :hints (("Goal" :in-theory (disable bx-formula-cands))))

(defthm faithful-formula-candidates-of-formula-candidates
  (equal (bx-formula-cands (bx-formula-cands candidates))
         (bx-formula-cands candidates)))

(defthm faithful-no-later-items-from-formula-candidates
  (equal (bx-later-items (bx-formula-cands candidates)) nil))

(defund faithful-direct-constrain-items (names owner pending wrld)
  (bx-constrain-items names owner (faithful-formula-pending pending) wrld))

(defund faithful-direct-event (ev encl pending defined translations wrld)
  (bx-event-items ev encl (faithful-formula-pending pending) defined
                  translations wrld))

(defthm faithful-first-value-of-direct-event
  (equal (mv-nth 0 (faithful-direct-event ev encl pending defined translations wrld))
         (car (faithful-direct-event ev encl pending defined translations wrld)))
  :hints (("Goal" :in-theory (enable mv-nth))))

(local
 (defthm faithful-append-associates
   (equal (append (append a b) c)
          (append a b c))))

(local
 (defthm faithful-constrain-items-split
   (equal (bx-constrain-items names owner pending wrld)
          (append (faithful-direct-constrain-items names owner pending wrld)
                  (bx-later-items (cdr (assoc-equal owner pending)))))
   :hints (("Goal"
            :in-theory (e/d (faithful-direct-constrain-items)
                            (constraint-info bx-formula-cands bx-later-items
                             faithful-formula-pending bx-constrain-stmt
                             bx-name-formulas bx-candidate-formulas
                             bx-sort-by-event fgetprop))))))

(defthmd faithful-direct-event-result
  (equal (car (faithful-direct-event ev encl pending defined translations wrld))
         (if (equal (bx-ev-type ev) 'encapsulate)
             (let ((names (bx-names (bx-ev-namex ev)))
                   (owner (bx-constrainer ev wrld)))
               (and (consp names)
                    (append
                     (and encl (not (eq encl owner))
                          (list (bx-note "encapsulate with a signature inside another"
                                         names)))
                     (faithful-direct-constrain-items names owner pending wrld))))
           (car (bx-event-items ev encl pending defined translations wrld))))
  :hints (("Goal"
           :in-theory (e/d (faithful-direct-event faithful-direct-constrain-items)
                           (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                            bx-names bx-constrainer bx-constrain-items
                            bx-program-defs bx-all-program-p bx-some-program-p
                            bx-all-constrained-p bx-some-constrained-p bx-constrained-p
                            bx-add-candidates bx-choose-items bx-definition-candidates
                            bx-define-items bx-stobj-items bx-reserve-items
                            bx-package-items bx-names-with-content bx-names-reserved
                            bx-mentions-some bx-conjuncts constraint-info fgetprop
                            faithful-formula-pending faithful-constrain-items-split))
           :do-not-induct t)))

(defthm faithful-event-items-split
  (equal (mv-nth 0 (bx-event-items ev encl pending defined translations wrld))
         (append (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                    translations wrld))
                 (if (and (eq (bx-ev-type ev) 'encapsulate)
                          (consp (bx-names (bx-ev-namex ev))))
                     (bx-later-items (cdr (assoc-equal (bx-constrainer ev wrld)
                                                      pending)))
                   nil)))
  :hints (("Goal"
           :in-theory (e/d (faithful-direct-event-result)
                           (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                            bx-names bx-constrainer bx-constrain-items
                            faithful-formula-pending faithful-direct-constrain-items
                            bx-program-defs bx-all-program-p bx-some-program-p
                            bx-all-constrained-p bx-some-constrained-p
                            bx-constrained-p bx-add-candidates bx-choose-items
                            bx-definition-candidates bx-define-items bx-stobj-items
                            bx-reserve-items bx-package-items bx-names-with-content
                            bx-names-reserved bx-mentions-some bx-conjuncts
                            constraint-info fgetprop))
           :do-not-induct t))
  :rule-classes nil)

; The search follows the event walk's deferrals. The first event whose
; items include the item must have produced it when no pending
; deferral already contains it.

(defund faithful-delay-items-p (encl items pending wrld)
  (and encl
       (intersectp-eq
        (bx-items-used items)
        (append (getprop encl 'siblings nil 'current-acl2-world wrld)
                (bx-items-introduced
                 (bx-later-items (cdr (assoc-equal encl pending))))))))

(defund faithful-next-pending (encl items pending wrld)
  (if (faithful-delay-items-p encl items pending wrld)
      (bx-add-candidates encl (list (list nil :after items)) pending)
    pending))

(defun faithful-deferred-item-p (item pending)
  (if (endp pending)
      nil
    (or (member-equal item (bx-later-items (cdar pending)))
        (faithful-deferred-item-p item (cdr pending)))))

(local
 (defthm faithful-deferred-item-in-bucket
   (implies (not (faithful-deferred-item-p item pending))
            (not (member-equal item (bx-later-items (cdr (assoc-equal owner
                                                                    pending))))))
   :hints (("Goal" :in-theory (disable bx-later-items)))))

(defthm faithful-later-items-of-append
  (equal (bx-later-items (append a b))
         (append (bx-later-items a) (bx-later-items b))))

(local
 (defthm faithful-deferred-item-absent-after-put
   (implies (and (not (faithful-deferred-item-p item pending))
                 (not (member-equal item (bx-later-items cands))))
            (not (faithful-deferred-item-p item (put-assoc-equal owner cands pending))))
   :hints (("Goal" :induct (put-assoc-equal owner cands pending)
            :in-theory (disable bx-later-items)))))

(local
 (defthm faithful-deferred-item-absent-after-add
   (implies (and (not (faithful-deferred-item-p item pending))
                 (not (member-equal item (bx-later-items cands))))
            (not (faithful-deferred-item-p item (bx-add-candidates owner cands pending))))
   :hints (("Goal"
            :in-theory (disable bx-later-items put-assoc-equal faithful-deferred-item-p)))))

(local
 (defthm faithful-definition-candidates-hold-no-items
   (equal (bx-later-items (bx-definition-candidates names wrld)) nil)
   :hints (("Goal" :in-theory (disable bx-formula-name)))))

(local
 (defthm faithful-event-preserves-deferred-item-absence
   (implies (not (faithful-deferred-item-p item pending))
            (not (faithful-deferred-item-p
                  item (mv-nth 1 (bx-event-items ev encl pending defined
                                                 translations wrld)))))
   :hints (("Goal"
            :in-theory (disable bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                                bx-names bx-constrainer bx-constrain-items
                                bx-program-defs bx-all-program-p bx-some-program-p
                                bx-all-constrained-p bx-some-constrained-p
                                bx-constrained-p bx-add-candidates bx-choose-items
                                bx-definition-candidates bx-define-items bx-stobj-items
                                bx-reserve-items bx-package-items bx-names-with-content
                                bx-names-reserved bx-mentions-some bx-conjuncts
                                constraint-info fgetprop faithful-deferred-item-p)
            :do-not-induct t))))

(local
 (defthm faithful-next-pending-preserves-item-absence
   (implies (and (not (member-equal item items))
                 (not (faithful-deferred-item-p item pending)))
            (not (faithful-deferred-item-p
                  item (faithful-next-pending encl items pending wrld))))
   :hints (("Goal"
            :in-theory (e/d (faithful-next-pending)
                            (bx-add-candidates faithful-deferred-item-p
                             bx-items-used bx-items-introduced fgetprop))))))

(local
 (defthm faithful-first-item-is-direct
   (implies (and (not (faithful-deferred-item-p item pending))
                 (member-equal item
                               (mv-nth 0 (bx-event-items ev encl pending defined
                                                          translations wrld))))
            (member-equal item
                          (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                             translations wrld))))
   :hints (("Goal"
            :use faithful-event-items-split
            :in-theory (disable bx-event-items bx-ev-type bx-ev-namex bx-names
                                bx-constrainer bx-later-items
                                faithful-deferred-item-p)
            :do-not-induct t))
   :rule-classes nil))

(defun faithful-item-origin (item pairs pending defined translations wrld)
  (if (endp pairs)
      nil
    (mv-let (items next-pending)
      (bx-event-items (caar pairs) (cdar pairs) pending defined
                      translations wrld)
      (if (member-equal item items)
          (list (caar pairs) (cdar pairs) pending defined)
        (faithful-item-origin item (cdr pairs)
                              (faithful-next-pending (cdar pairs) items next-pending wrld)
                              (bx-add-defined items defined)
                              translations wrld)))))

(defthm faithful-origin-produces-item
  (let ((origin (faithful-item-origin item pairs pending defined
                                      translations wrld)))
    (implies (and origin (not (faithful-deferred-item-p item pending)))
             (member-equal item
                           (mv-nth 0 (faithful-direct-event
                                      (car origin) (cadr origin)
                                      (caddr origin) (cadddr origin)
                                      translations wrld)))))
  :hints (("Goal"
           :induct (faithful-item-origin item pairs pending defined
                                         translations wrld)
           :in-theory (disable bx-event-items bx-add-defined member-equal
                               faithful-deferred-item-p))
          ("Subgoal *1/2"
           :use ((:instance faithful-first-item-is-direct
                            (ev (caar pairs)) (encl (cdar pairs))))))
  :rule-classes nil)

(defthmd faithful-bx-items-step
  (implies (consp pairs)
           (mv-let (items next-pending)
             (bx-event-items (caar pairs) (cdar pairs) pending defined
                             translations wrld)
             (equal (bx-items pairs pending defined translations wrld acc)
                    (bx-items (cdr pairs)
                              (faithful-next-pending (cdar pairs) items next-pending wrld)
                              (bx-add-defined items defined)
                              translations wrld
                              (if (faithful-delay-items-p (cdar pairs) items
                                                          next-pending wrld)
                                  acc
                                (revappend items acc))))))
  :hints (("Goal"
           :expand ((bx-items pairs pending defined translations wrld acc))
           :in-theory (e/d (faithful-next-pending faithful-delay-items-p)
                           (bx-items bx-event-items bx-add-defined bx-add-candidates
                            bx-items-used bx-items-introduced bx-later-items
                            intersectp-equal assoc-equal binary-append fgetprop
                            revappend))
           :do-not-induct t)))

(defthm faithful-bx-items-base
  (implies (atom pairs)
           (equal (bx-items pairs pending defined translations wrld acc)
                  (reverse acc)))
  :hints (("Goal" :expand ((bx-items pairs pending defined translations wrld acc)))))

(defthm faithful-item-has-origin
  (implies (and (member-equal item
                              (bx-items pairs pending defined translations
                                        wrld acc))
                (not (member-equal item acc))
                (not (stringp acc)))
           (faithful-item-origin item pairs pending defined translations
                                 wrld))
  :hints (("Goal"
           :induct (bx-items pairs pending defined translations wrld acc)
           :in-theory (e/d (faithful-next-pending faithful-delay-items-p)
                           (bx-event-items bx-add-defined bx-add-candidates
                            bx-items-used bx-items-introduced bx-later-items
                            intersectp-equal assoc-equal binary-append fgetprop
                            member-equal revappend reverse))))
  :rule-classes nil)

(defthm faithful-member-of-bx-select
  (implies (and key (member-equal line (bx-select key items)))
           (member-equal (cons key line) items))
  :hints (("Goal" :induct (bx-select key items))))

(defund faithful-statement-origin (line lo hi translations wrld)
  (faithful-item-origin
   (cons :stmt line)
   (bx-enclose (reverse (bx-events wrld lo hi nil)) nil nil wrld)
   nil nil translations wrld))

(defthm faithful-statement-origin-produces-line
  (let ((origin (faithful-statement-origin line lo hi translations wrld)))
    (implies origin
             (member-equal (cons :stmt line)
                           (mv-nth 0 (faithful-direct-event
                                      (car origin) (cadr origin)
                                      (caddr origin) (cadddr origin)
                                      translations wrld)))))
  :hints (("Goal"
           :use ((:instance faithful-origin-produces-item
                            (item (cons :stmt line))
                            (pairs (bx-enclose
                                    (reverse (bx-events wrld lo hi nil))
                                    nil nil wrld))
                            (pending nil) (defined nil)))
           :in-theory (e/d (faithful-statement-origin)
                           (faithful-item-origin bx-enclose bx-events
                            bx-event-items))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm faithful-origin-of-range
   (implies (member-equal line
                          (bx-select :stmt (bx-range-items lo hi translations wrld)))
            (faithful-statement-origin line lo hi translations wrld))
   :hints (("Goal"
            :use ((:instance faithful-item-has-origin
                             (item (cons :stmt line))
                             (pairs (bx-enclose
                                     (reverse (bx-events wrld lo hi nil))
                                     nil nil wrld))
                             (pending nil) (defined nil) (acc nil))
                  (:instance faithful-member-of-bx-select
                             (key :stmt)
                             (items (bx-range-items lo hi translations wrld))))
            :in-theory (e/d (faithful-statement-origin)
                            (bx-items bx-select bx-enclose bx-events
                             faithful-item-origin faithful-member-of-bx-select))
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-library-statement-has-origin
  (implies (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
           (faithful-statement-origin line 0 hi translations wrld))
  :hints (("Goal"
           :use ((:instance faithful-origin-of-range (lo 0)))
           :in-theory (e/d (bx-library-lines bx-range-items)
                           (bx-events bx-enclose bx-items bx-select bx-not-ground
                            bx-library-order bx-ground-tables bx-check-stmts
                            bx-ground-defines bx-attachment-pairs bx-attach-lines
                            bx-runnable bx-library-program-order))
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-book-statement-has-origin
  (implies (member-equal line
                         (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                  translations books-dir cbd wrld)))
           (faithful-statement-origin line lo hi translations wrld))
  :hints (("Goal"
           :use faithful-origin-of-range
           :in-theory (e/d (bx-book-lines)
                           (bx-events bx-enclose bx-items bx-select bx-not-ground
                            bx-library-order bx-ground-tables bx-check-stmts
                            bx-book-notes bx-attachment-pairs bx-attach-lines
                            bx-runnable bx-range-items bx-event-aids))
           :do-not-induct t))
  :rule-classes nil)

; The witness is an event landmark of the supplied world.

(defund faithful-event-landmark-p (event wrld)
  (member-equal (list* 'event-landmark 'global-value event) wrld))

(local
 (defthm faithful-landmark-of-bx-events
   (implies (and (not (member-equal event acc))
                 (member-equal event (bx-events wrld lo hi acc)))
            (faithful-event-landmark-p event wrld))
   :hints (("Goal" :induct (bx-events wrld lo hi acc)
            :in-theory (e/d (faithful-event-landmark-p) (bx-ev-number))))
   :rule-classes nil))

(local
 (defthm faithful-key-of-bx-enclose
   (implies (and (not (member-equal event (strip-cars acc)))
                 (member-equal event (strip-cars (bx-enclose events stack acc wrld))))
            (member-equal event events))
   :hints (("Goal" :induct (bx-enclose events stack acc wrld)
            :in-theory (disable bx-ev-depth bx-ev-type bx-pop
                                bx-first-constrainer bx-constrainer)))
   :rule-classes nil))

(defthm faithful-event-of-item-origin
  (let ((origin (faithful-item-origin item pairs pending defined
                                      translations wrld)))
    (implies origin (member-equal (car origin) (strip-cars pairs))))
  :hints (("Goal" :induct (faithful-item-origin item pairs pending defined
                                               translations wrld)
           :in-theory (disable bx-event-items bx-add-defined member-equal))
          ("Subgoal *1/2" :expand ((member-equal (caar pairs) (strip-cars pairs)))))
  :rule-classes nil)

(defthm faithful-landmark-of-statement-origin
  (let ((origin (faithful-statement-origin line lo hi translations wrld)))
    (implies origin (faithful-event-landmark-p (car origin) wrld)))
  :hints (("Goal"
           :use ((:instance faithful-event-of-item-origin
                            (item (cons :stmt line))
                            (pairs (bx-enclose
                                    (reverse (bx-events wrld lo hi nil))
                                    nil nil wrld))
                            (pending nil) (defined nil))
                 (:instance faithful-key-of-bx-enclose
                            (event (car (faithful-statement-origin
                                        line lo hi translations wrld)))
                            (events (reverse (bx-events wrld lo hi nil)))
                            (stack nil) (acc nil))
                 (:instance faithful-landmark-of-bx-events
                            (event (car (faithful-statement-origin
                                        line lo hi translations wrld)))
                            (acc nil)))
           :in-theory (e/d (faithful-statement-origin)
                           (bx-events bx-enclose faithful-item-origin))
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-event-landmark-of-range
  (implies (member-equal event
                         (strip-cars (bx-enclose (reverse (bx-events wrld lo hi nil))
                                                 nil nil wrld)))
           (faithful-event-landmark-p event wrld))
  :hints (("Goal"
           :use ((:instance faithful-key-of-bx-enclose
                            (events (reverse (bx-events wrld lo hi nil)))
                            (stack nil) (acc nil))
                 (:instance faithful-landmark-of-bx-events (acc nil)))
           :in-theory (disable bx-events bx-enclose)
           :do-not-induct t))
  :rule-classes nil)
