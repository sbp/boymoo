(in-package "ACL2")

(include-book "faithful-program-items")

; Filtering leaves each selected item intact. The library also writes
; its ground definitions and the logical definitions in statement order.

(local
 (defthm faithful-selected-line-of-bx-words
   (implies (member-equal line (bx-words words lines))
            (and (member-equal line lines) (member-equal (car line) words)))))

(local
 (defthm faithful-selected-line-of-bx-program-only
   (implies (member-equal line (bx-program-only lines wrld))
            (member-equal line lines))
   :hints (("Goal" :in-theory (disable bx-all-program-p)))))

(local
 (defthm faithful-selected-line-of-bx-runnable
   (implies (member-equal line (bx-runnable lines))
            (member-equal line lines))
   :hints (("Goal" :in-theory (disable bx-introduced)))))

(defthm faithful-attach-line-word
  (implies (member-equal line (bx-attach-lines pairs except))
           (equal (car line) "attach")))

(local
 (defthm faithful-library-program-order-sources
   (implies (member-equal line
                          (bx-runnable (bx-library-program-order progs ordered wrld)))
            (or (and (equal (car line) "define") (member-equal line ordered))
                (member-equal line progs)))
   :hints (("Goal"
            :use ((:instance faithful-selected-line-of-bx-runnable
                             (lines (bx-library-program-order progs ordered wrld)))
                  (:instance faithful-selected-line-of-bx-words
                             (words '("define")) (lines ordered))
                  (:instance faithful-selected-line-of-bx-program-only
                             (lines progs)))
            :in-theory (disable bx-runnable bx-words bx-program-only
                                faithful-selected-line-of-bx-runnable
                                faithful-selected-line-of-bx-words
                                faithful-selected-line-of-bx-program-only)
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-library-program-sources
  (implies (member-equal line (mv-nth 1 (bx-library-lines ground hi translations wrld)))
           (or (member-equal line (bx-ground-defines ground wrld))
               (and (equal (car line) "define")
                    (member-equal line (mv-nth 0 (bx-library-lines
                                                   ground hi translations wrld))))
               (member-equal line (bx-select :prog (bx-range-items 0 hi translations wrld)))
               (member-equal line (bx-attach-lines (bx-attachment-pairs wrld) nil))))
  :hints (("Goal"
           :use ((:instance faithful-library-program-order-sources
                            (progs (bx-not-ground
                                    (bx-select :prog (bx-range-items 0 hi translations wrld))
                                    ground))
                            (ordered (mv-nth 0 (bx-library-lines ground hi translations wrld)))))
           :in-theory (disable bx-events bx-enclose bx-items bx-select bx-not-ground
                               bx-library-order bx-ground-tables bx-check-stmts bx-runnable
                               bx-ground-defines bx-attachment-pairs bx-attach-lines
                               bx-library-program-order)
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-book-program-sources
  (implies (member-equal line (mv-nth 1 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir cbd wrld)))
           (or (member-equal line (bx-select :prog (bx-range-items lo hi translations wrld)))
               (member-equal line (bx-attach-lines (bx-attachment-pairs wrld)
                                                  (bx-attachment-pairs
                                                   (bx-world-at boot-hi wrld))))))
  :hints (("Goal"
           :use ((:instance faithful-selected-line-of-bx-runnable
                            (lines (bx-select :prog (bx-range-items lo hi translations wrld)))))
           :in-theory (disable bx-events bx-enclose bx-items bx-select bx-not-ground
                               bx-library-order bx-ground-tables bx-check-stmts
                               bx-book-notes bx-attachment-pairs bx-attach-lines
                               bx-runnable bx-world-at bx-range-items bx-event-aids
                               faithful-selected-line-of-bx-runnable)
           :do-not-induct t))
  :rule-classes nil)

; Ground functions are read as logical definitions from the world.

(defthm faithful-ground-program-line
  (implies (and (member-equal line (bx-ground-defines ground wrld))
                (or (not bodies-p)
                    (and (plist-worldp-with-formals wrld)
                         (faithful-nonprogram-fns-p ground wrld))))
           (and (equal (car line) "define")
                (or (not bodies-p)
                    (faithful-program-definitions-p (cdr (cadr line)) translations wrld))))
  :hints (("Goal" :induct (bx-ground-defines ground wrld)
           :in-theory (e/d (faithful-program-definition-p)
                           (bx-rulers formals fgetprop plist-worldp-with-formals)))))

; A selected definition belongs to an event of the range. Use that
; event's symbol classes and stored bodies, including those of stobjs.

(local
 (defthm faithful-program-items-of-world-event
   (implies (and (faithful-event-landmark-p ev wrld)
                 (or (not bodies-p)
                     (and (plist-worldp-with-formals wrld)
                          (faithful-stobj-program-world-p wrld))))
            (faithful-program-items-p
             (mv-nth 0 (faithful-direct-event ev encl pending defined translations wrld))
             translations wrld bodies-p))
   :hints (("Goal"
            :use (faithful-program-items-of-event
                  (:instance faithful-event-type-reader (event ev))
                  (:instance faithful-event-name-reader (event ev))
                  (:instance faithful-stobj-program-record-from-world (event ev)))
            :in-theory (disable bx-event-items bx-ev-type bx-ev-namex bx-names
                                access-event-tuple-type faithful-event-names
                                faithful-program-items-p faithful-program-items-of-event
                                faithful-stobj-program-names-p plist-worldp-with-formals)
            :do-not-induct t))
   :rule-classes nil))

(defund faithful-range-item-origin (key line lo hi translations wrld)
  (faithful-item-origin
   (cons key line)
   (bx-enclose (reverse (bx-events wrld lo hi nil)) nil nil wrld)
   nil nil translations wrld))

(local
 (defthm faithful-selected-line-has-origin
   (implies (and key
                 (member-equal line (bx-select key (bx-range-items lo hi translations wrld))))
            (faithful-range-item-origin key line lo hi translations wrld))
   :hints (("Goal"
            :use ((:instance faithful-item-has-origin
                             (item (cons key line))
                             (pairs (bx-enclose (reverse (bx-events wrld lo hi nil))
                                                nil nil wrld))
                             (pending nil) (defined nil) (acc nil))
                  (:instance faithful-member-of-bx-select
                             (items (bx-range-items lo hi translations wrld))))
            :in-theory (e/d (faithful-range-item-origin)
                            (bx-items bx-select bx-enclose bx-events faithful-item-origin
                             faithful-member-of-bx-select))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-range-item-origin-is-landmark
   (let ((origin (faithful-range-item-origin key line lo hi translations wrld)))
     (implies origin (faithful-event-landmark-p (car origin) wrld)))
   :hints (("Goal"
            :use ((:instance faithful-event-of-item-origin
                             (item (cons key line))
                             (pairs (bx-enclose (reverse (bx-events wrld lo hi nil))
                                                nil nil wrld))
                             (pending nil) (defined nil))
                  (:instance faithful-event-landmark-of-range
                             (event (car (faithful-range-item-origin
                                          key line lo hi translations wrld)))))
            :in-theory (e/d (faithful-range-item-origin)
                            (bx-enclose bx-events faithful-item-origin))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-range-item-origin-produces-line
   (let ((origin (faithful-range-item-origin key line lo hi translations wrld)))
     (implies origin
              (member-equal (cons key line)
                            (mv-nth 0 (faithful-direct-event
                                       (car origin) (cadr origin)
                                       (caddr origin) (cadddr origin)
                                       translations wrld)))))
   :hints (("Goal"
            :use ((:instance faithful-origin-produces-item
                             (item (cons key line))
                             (pairs (bx-enclose (reverse (bx-events wrld lo hi nil))
                                                nil nil wrld))
                             (pending nil) (defined nil)))
            :in-theory (e/d (faithful-range-item-origin)
                            (bx-enclose bx-events bx-event-items faithful-item-origin))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-statement-origin-is-range-origin
   (equal (faithful-statement-origin line lo hi translations wrld)
          (faithful-range-item-origin :stmt line lo hi translations wrld))
   :hints (("Goal"
            :in-theory (e/d (faithful-statement-origin faithful-range-item-origin)
                            (faithful-item-origin bx-events bx-enclose))))))

(local
 (defthm faithful-program-line-of-range-origin
   (let ((origin (faithful-range-item-origin key line lo hi translations wrld)))
     (implies (and origin
                   (or (eq key :prog)
                       (and (eq key :stmt) (equal (car line) "define")))
                   (or (not bodies-p)
                       (and (plist-worldp-with-formals wrld)
                            (faithful-stobj-program-world-p wrld))))
              (and (equal (car line) "define")
                   (or (not bodies-p)
                       (faithful-program-definitions-p (cdr (cadr line))
                                                       translations wrld)))))
   :hints (("Goal"
            :use (faithful-range-item-origin-is-landmark
                  faithful-range-item-origin-produces-line
                  (:instance faithful-program-items-of-world-event
                             (ev (car (faithful-range-item-origin
                                       key line lo hi translations wrld)))
                             (encl (cadr (faithful-range-item-origin
                                         key line lo hi translations wrld)))
                             (pending (caddr (faithful-range-item-origin
                                             key line lo hi translations wrld)))
                             (defined (cadddr (faithful-range-item-origin
                                               key line lo hi translations wrld))))
                  (:instance faithful-program-line-of-items
                             (items (mv-nth 0 (faithful-direct-event
                                              (car (faithful-range-item-origin
                                                    key line lo hi translations wrld))
                                              (cadr (faithful-range-item-origin
                                                     key line lo hi translations wrld))
                                              (caddr (faithful-range-item-origin
                                                      key line lo hi translations wrld))
                                              (cadddr (faithful-range-item-origin
                                                       key line lo hi translations wrld))
                                              translations wrld)))))
            :in-theory (disable bx-event-items faithful-program-items-p
                                faithful-program-definitions-p plist-worldp-with-formals)
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-program-line-from-range
  (implies (and (member-equal line (bx-select :prog (bx-range-items lo hi translations wrld)))
                (or (not bodies-p)
                    (and (plist-worldp-with-formals wrld)
                         (faithful-stobj-program-world-p wrld))))
           (and (equal (car line) "define")
                (or (not bodies-p)
                    (faithful-program-definitions-p (cdr (cadr line)) translations wrld))))
  :hints (("Goal"
           :use ((:instance faithful-selected-line-has-origin (key :prog))
                 (:instance faithful-program-line-of-range-origin (key :prog)))
           :in-theory (disable bx-range-items bx-select faithful-program-definitions-p
                               plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

; Each program definition agrees with the appropriate stored or supplied
; body. The runner uses the list of definitions and ignores the rulers.

(defthm faithful-library-program-define
  (implies
   (and (equal (car line) "define")
        (member-equal line (mv-nth 1 (bx-library-lines ground hi translations wrld)))
        (plist-worldp-with-formals wrld)
        (faithful-stobj-program-world-p wrld)
        (faithful-nonprogram-fns-p ground wrld))
   (faithful-program-definitions-p (cdr (cadr line)) translations wrld))
  :hints (("Goal"
           :use (faithful-library-program-sources
                 faithful-library-statement-has-origin
                 (:instance faithful-ground-program-line (bodies-p t))
                 (:instance faithful-program-line-of-range-origin
                            (key :stmt) (lo 0) (bodies-p t))
                 (:instance faithful-program-line-from-range (lo 0) (bodies-p t)))
           :in-theory (disable bx-library-lines bx-range-items bx-select bx-attach-lines
                               bx-ground-defines bx-attachment-pairs
                               faithful-program-definitions-p faithful-nonprogram-fns-p
                               plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-book-program-define
  (implies
   (and (equal (car line) "define")
        (member-equal line (mv-nth 1 (bx-book-lines ground boot-hi lo hi
                                                   translations books-dir cbd wrld)))
        (plist-worldp-with-formals wrld)
        (faithful-stobj-program-world-p wrld))
   (faithful-program-definitions-p (cdr (cadr line)) translations wrld))
  :hints (("Goal"
           :use (faithful-book-program-sources
                 (:instance faithful-program-line-from-range (bodies-p t)))
           :in-theory (disable bx-book-lines bx-range-items bx-select bx-attach-lines
                               bx-attachment-pairs bx-world-at
                               faithful-program-definitions-p plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)
