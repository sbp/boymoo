(in-package "ACL2")

(include-book "faithful-definitions")
(include-book "system/kestrel" :dir :system)

(verify-termination access-event-tuple-type)
(verify-termination access-event-tuple-form)

; These comparisons let the proof refer to ACL2's event record without
; using the exporter's readers in the world predicates.

(local
 (defthm faithful-signature-reader
   (equal (bx-signature-fns signatures)
          (signature-fns signatures))))

(defun faithful-event-names (event)
  (let ((names (access-event-tuple-namex event)))
    (cond ((eql names 0) nil)
          ((or (symbolp names) (stringp names)) (list names))
          (t names))))

(defthm faithful-event-type-reader
  (equal (bx-ev-type event) (access-event-tuple-type event))
  :rule-classes nil)

(defthm faithful-event-namex-reader
  (equal (bx-ev-namex event) (access-event-tuple-namex event))
  :hints (("Goal" :in-theory (disable bx-signature-fns signature-fns
                                     strip-cadrs strip-cars)))
  :rule-classes nil)

(defthm faithful-event-name-reader
  (equal (bx-names (bx-ev-namex event)) (faithful-event-names event))
  :hints (("Goal" :use faithful-event-namex-reader
           :in-theory (disable bx-ev-namex access-event-tuple-namex)))
  :rule-classes nil)

(defthm faithful-event-form-reader
  (equal (bx-ev-form event) (access-event-tuple-form event))
  :rule-classes nil)

; A named fact or choice event has its formula in the current world.

(defund faithful-fact-event-record-p (event wrld)
  (let ((name (car (faithful-event-names event))))
    (case (access-event-tuple-type event)
      ((defthm defaxiom) (getprop name 'theorem nil 'current-acl2-world wrld))
      (defchoose (getprop name 'defchoose-axiom nil 'current-acl2-world wrld))
      (otherwise t))))

(defun faithful-fact-records-p (triples wrld)
  (if (endp triples)
      t
    (and (or (not (and (eq (caar triples) 'event-landmark)
                       (eq (cadar triples) 'global-value)))
             (faithful-fact-event-record-p (cddar triples) wrld))
         (faithful-fact-records-p (cdr triples) wrld))))

(defund faithful-fact-world-p (wrld)
  (faithful-fact-records-p wrld wrld))

(local
 (defthm faithful-fact-record-of-landmark
   (implies (and (faithful-fact-records-p triples wrld)
                 (faithful-event-landmark-p event triples))
            (faithful-fact-event-record-p event wrld))
   :hints (("Goal" :induct (faithful-fact-records-p triples wrld)
            :in-theory (enable faithful-event-landmark-p)))))

(defthm faithful-fact-record-from-world
  (implies (and (faithful-fact-world-p wrld)
                (faithful-event-landmark-p event wrld))
           (faithful-fact-event-record-p event wrld))
  :hints (("Goal" :in-theory (enable faithful-fact-world-p)))
  :rule-classes nil)

; A named fact line has a formula present at the name it carries.

(local
 (defthm faithful-named-fact-record-of-event
   (implies (and (member-equal (car line) '("theorem" "axiom"))
                 (faithful-fact-event-record-p ev wrld)
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                          translations wrld))))
            (getprop (caadr line) 'theorem nil 'current-acl2-world wrld))
   :hints (("Goal"
            :use (faithful-statement-word-of-event
                  (:instance faithful-event-type-reader (event ev))
                  (:instance faithful-event-name-reader (event ev)))
            :in-theory (e/d (faithful-direct-event-result faithful-fact-event-record-p)
                            (bx-names-reserved bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                             access-event-tuple-type faithful-event-names bx-names
                             bx-programp bx-all-program-p bx-some-program-p
                             bx-constrained-p bx-all-constrained-p
                             bx-some-constrained-p bx-program-defs bx-define-items
                             bx-add-candidates bx-stobj-items fgetprop bx-conjuncts
                             bx-mentions-some constraint-info bx-choose-items
                             bx-constrain-items bx-package-items bx-reserve-items
                             bx-names-with-content))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-named-fact-record-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (member-equal (car line) '("theorem" "axiom"))
                   (faithful-fact-world-p wrld)
                   origin)
              (getprop (caadr line) 'theorem nil 'current-acl2-world wrld)))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  faithful-landmark-of-statement-origin
                  (:instance faithful-fact-record-from-world
                             (event (car (faithful-statement-origin
                                          line lo hi translations wrld))))
                  (:instance faithful-named-fact-record-of-event
                             (ev (car (faithful-statement-origin
                                       line lo hi translations wrld)))
                             (encl (cadr (faithful-statement-origin
                                         line lo hi translations wrld)))
                             (pending (caddr (faithful-statement-origin
                                             line lo hi translations wrld)))
                             (defined (cadddr (faithful-statement-origin
                                               line lo hi translations wrld)))))
            :in-theory (disable bx-event-items fgetprop)
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-fact-statement-has-world-record
  (implies
   (and (member-equal (car line) '("theorem" "axiom"))
        (faithful-fact-world-p wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (getprop (caadr line) 'theorem nil 'current-acl2-world wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-named-fact-record-of-origin (lo 0))
                 faithful-named-fact-record-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines fgetprop)
           :do-not-induct t))
  :rule-classes nil)
