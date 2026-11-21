(in-package "ACL2")

(include-book "faithful-constraint-names")

; These ACL2 properties keep a name in use without adding a function
; equation or a formula. STOBJ-LIVE-VAR names the live object variable.

(defund faithful-reserve-data-p (args wrld)
  (let ((name (car args)))
    (and (equal args (list name))
         (or (getprop name 'macro-body nil 'current-acl2-world wrld)
             (getprop name 'const nil 'current-acl2-world wrld)
             (getprop name 'label nil 'current-acl2-world wrld)
             (getprop name 'theory nil 'current-acl2-world wrld)
             (getprop name 'stobj nil 'current-acl2-world wrld)
             (getprop name 'stobj-live-var nil 'current-acl2-world wrld)))))

; The reserved names from a single-threaded object are accumulated
; apart from its defined functions.

(local
 (defthm faithful-reserved-name-from-property
   (implies (bx-reserve-kind-p name wrld)
            (faithful-reserve-data-p (list name) wrld))
   :hints (("Goal" :in-theory (e/d (faithful-reserve-data-p) (fgetprop))))))

(local
 (defthm faithful-reserve-data-of-items
   (implies (and (equal (car line) "reserve")
                 (member-equal (cons :stmt line) (bx-reserve-items names wrld)))
            (faithful-reserve-data-p (cadr line) wrld))
   :hints (("Goal" :in-theory (disable bx-reserve-kind-p)))))

(local
 (defthm faithful-no-reserve-in-bx-define-items
   (implies (equal (car line) "reserve")
            (not (member-equal (cons :stmt line) (bx-define-items fns wrld))))
   :hints (("Goal" :in-theory (disable bx-same-rulers bx-defs bx-rulers)))))

(local
 (defthm faithful-no-reserve-in-bx-stobj-definitions
   (implies (equal (car line) "reserve")
            (not (member-equal (cons :stmt line)
                               (bx-stobj-define-items fns wrld))))
   :hints (("Goal" :in-theory (disable bx-define-items)))))

(local
 (defthm faithful-reserve-data-of-stobj-items
   (implies (and (equal (car line) "reserve")
                 (not (stringp acc))
                 (implies (member-equal (cons :stmt line) acc)
                          (faithful-reserve-data-p (cadr line) wrld))
                 (member-equal (cons :stmt line)
                               (bx-stobj-items names defined fns-acc wrld acc)))
            (faithful-reserve-data-p (cadr line) wrld))
   :hints (("Goal"
            :induct (bx-stobj-items names defined fns-acc wrld acc)
            :in-theory (disable bx-stobj-define-items bx-exec bx-local-order
                                bx-reserve-kind-p bx-function-p bx-programp
                                hons-get formals fgetprop)))
   :rule-classes nil))

; Trace a reserve statement to one of the events that holds its name.

(local
 (defthm faithful-reserve-of-event
   (implies (and (equal (car line) "reserve")
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                          translations wrld))))
            (faithful-reserve-data-p (cadr line) wrld))
   :hints (("Goal"
            :use (faithful-statement-word-of-event
                  (:instance faithful-reserve-data-of-stobj-items
                             (names (bx-names (bx-ev-namex ev)))
                             (fns-acc nil) (acc nil)))
            :in-theory (e/d (faithful-direct-event-result)
                            (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                                bx-names bx-programp bx-all-program-p
                                bx-some-program-p bx-constrained-p
                                bx-all-constrained-p bx-some-constrained-p
                                bx-program-defs bx-define-items bx-add-candidates
                                bx-stobj-items fgetprop bx-conjuncts
                                bx-mentions-some constraint-info bx-choose-items
                                bx-constrain-items bx-package-items
                                bx-reserve-items bx-names-with-content
                             bx-names-reserved))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-reserve-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (equal (car line) "reserve")
                   origin)
              (faithful-reserve-data-p (cadr line) wrld)))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  (:instance faithful-reserve-of-event
                             (ev (car (faithful-statement-origin
                                       line lo hi translations wrld)))
                             (encl (cadr (faithful-statement-origin
                                         line lo hi translations wrld)))
                             (pending (caddr (faithful-statement-origin
                                             line lo hi translations wrld)))
                             (defined (cadddr (faithful-statement-origin
                                               line lo hi translations wrld)))))
            :in-theory (disable bx-event-items)
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-reserve-statement
  (implies
   (and (equal (car line) "reserve")
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-reserve-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-reserve-of-origin (lo 0))
                 faithful-reserve-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines)
           :do-not-induct t))
  :rule-classes nil)
