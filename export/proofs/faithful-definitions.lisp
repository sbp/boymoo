(in-package "ACL2")

(include-book "faithful-kinds")

; A definition carries the stored formals and unnormalized body of each
; function. A singleton has its own ruler-extenders. A clique shares the
; field taken from the justification of its first function.

(defund faithful-ruler-extenders (fn wrld)
  (let ((record (getprop fn 'justification nil 'current-acl2-world wrld)))
    (if record (access justification record :ruler-extenders) nil)))

(defun faithful-definition-bodies-p (definitions wrld)
  (if (atom definitions)
      (null definitions)
    (let ((fn (caar definitions)))
      (and (equal (car definitions)
                  (list fn
                        (getprop fn 'formals nil 'current-acl2-world wrld)
                        (getprop fn 'unnormalized-body nil 'current-acl2-world wrld)))
           (faithful-definition-bodies-p (cdr definitions) wrld)))))

(defund faithful-definition-data-p (args wrld)
  (let ((definitions (cdr args)))
    (and (consp definitions)
         (equal (car args)
                (faithful-ruler-extenders (caar definitions) wrld))
         (faithful-definition-bodies-p definitions wrld))))

; FORMALS is the system accessor for the FORMALS property.

(defthm faithful-formals-getprop
  (implies (plist-worldp-with-formals wrld)
           (equal (formals fn wrld)
                  (getprop fn 'formals nil 'current-acl2-world wrld)))
  :hints (("Goal" :induct (fgetprop fn 'formals nil wrld)
           :in-theory (enable formals plist-worldp-with-formals))))

(local
 (defthm faithful-bx-defs-data
   (implies (plist-worldp-with-formals wrld)
            (faithful-definition-bodies-p (bx-defs fns wrld) wrld))
   :hints (("Goal" :in-theory (disable formals fgetprop)))))

(local
 (defthm faithful-first-bx-def
   (implies (consp fns)
            (equal (caar (bx-defs fns wrld))
                   (car fns)))
   :hints (("Goal" :in-theory (disable formals fgetprop)))))

(local
 (defthm faithful-consp-bx-defs
   (equal (consp (bx-defs fns wrld))
          (consp fns))
   :hints (("Goal" :in-theory (disable formals fgetprop)))))

(local
 (defthm faithful-ruler-extenders-of-bx-rulers
   (equal (bx-rulers fn wrld)
          (faithful-ruler-extenders fn wrld))
   :hints (("Goal" :in-theory (e/d (faithful-ruler-extenders) (fgetprop))))))

; The ordinary constructor serves one definition or a clique. The
; single-threaded object constructor uses it on singletons.

(local
 (defthm faithful-definition-of-bx-define-items
   (implies (and (plist-worldp-with-formals wrld)
                 (consp fns)
                 (equal (car line) "define")
                 (member-equal (cons :stmt line) (bx-define-items fns wrld)))
            (faithful-definition-data-p (cadr line) wrld))
   :hints (("Goal"
            :in-theory (e/d (faithful-definition-data-p)
                            (bx-defs bx-same-rulers bx-rulers
                             faithful-definition-bodies-p formals fgetprop))))
   :rule-classes ((:forward-chaining
                   :trigger-terms
                   ((member-equal (cons :stmt line) (bx-define-items fns wrld)))))))

(local
 (defthm faithful-definition-of-bx-stobj-define-items
   (implies (and (plist-worldp-with-formals wrld)
                 (equal (car line) "define")
                 (member-equal (cons :stmt line)
                               (bx-stobj-define-items fns wrld)))
            (faithful-definition-data-p (cadr line) wrld))
   :hints (("Goal" :in-theory (disable bx-define-items plist-worldp-with-formals)))
   :rule-classes ((:forward-chaining
                   :trigger-terms
                   ((member-equal (cons :stmt line) (bx-stobj-define-items fns wrld)))))))

(local
 (defthm faithful-no-define-in-bx-stobj-accumulator
   (implies (and (equal (car line) "define")
                 (not (stringp acc))
                 (not (member-equal (cons :stmt line) acc))
                 (plist-worldp-with-formals wrld)
                 (member-equal (cons :stmt line)
                               (bx-stobj-items names defined fns-acc wrld acc)))
            (faithful-definition-data-p (cadr line) wrld))
   :hints (("Goal"
            :induct (bx-stobj-items names defined fns-acc wrld acc)
            :in-theory (disable bx-stobj-define-items bx-exec bx-local-order
                                bx-reserve-kind-p bx-function-p bx-programp
                                hons-get formals fgetprop)))
   :rule-classes nil))

(local
 (defthm faithful-nonempty-if-not-all-constrained
   (implies (not (bx-all-constrained-p fns wrld))
            (consp fns))
   :rule-classes :forward-chaining))

; Only definition events and single-threaded object events write
; definition statements.

(local
 (defthm faithful-definition-of-event
   (implies (and (equal (car line) "define")
                 (plist-worldp-with-formals wrld)
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                          translations wrld))))
            (faithful-definition-data-p (cadr line) wrld))
   :hints (("Goal"
            :use (faithful-statement-word-of-event
                  (:instance faithful-no-define-in-bx-stobj-accumulator
                             (names (bx-names (bx-ev-namex ev)))
                             (fns-acc nil) (acc nil)))
            :in-theory (e/d (faithful-direct-event-result)
                            (bx-ev-type bx-ev-namex bx-ev-symbol-class
                                bx-ev-form bx-names bx-programp bx-all-program-p
                                bx-some-program-p bx-constrained-p
                                bx-all-constrained-p bx-some-constrained-p
                                bx-program-defs bx-define-items bx-add-candidates
                                bx-stobj-items fgetprop bx-define-items
                                bx-conjuncts bx-mentions-some constraint-info
                                bx-choose-items bx-constrain-items bx-package-items
                                bx-reserve-items bx-names-with-content bx-names-reserved))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-definition-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (equal (car line) "define")
                   (plist-worldp-with-formals wrld)
                   origin)
              (faithful-definition-data-p (cadr line) wrld)))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  (:instance faithful-definition-of-event
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

(defthm faithful-define-statement
  (implies
   (and (equal (car line) "define")
        (plist-worldp-with-formals wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-definition-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-definition-of-origin (lo 0))
                 faithful-definition-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

; The exception for a clique is exact. Its shared field is correct for
; each member whose stored ruler-extenders agree with the first member's.

(defthm faithful-define-ruler-extender-exception
  (implies
   (and (equal (car line) "define")
        (plist-worldp-with-formals wrld)
        (member-equal definition (cdr (cadr line)))
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (iff (equal (car (cadr line))
               (faithful-ruler-extenders (car definition) wrld))
        (equal (faithful-ruler-extenders (caadr (cadr line)) wrld)
               (faithful-ruler-extenders (car definition) wrld))))
  :hints (("Goal"
           :use faithful-define-statement
           :in-theory (e/d (faithful-definition-data-p)
                           (bx-library-lines bx-book-lines plist-worldp-with-formals
                            faithful-definition-bodies-p))
           :do-not-induct t))
  :rule-classes nil)

; Both kinds of named fact have a formula in the THEOREM property.

(defund faithful-formula-data-p (args wrld)
  (let ((name (car args)))
    (equal args (list name (getprop name 'theorem nil 'current-acl2-world wrld)))))

(local
 (defthm faithful-fact-of-event
   (implies (and (member-equal (car line) '("theorem" "axiom"))
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                          translations wrld))))
            (faithful-formula-data-p (cadr line) wrld))
   :hints (("Goal"
            :use faithful-statement-word-of-event
            :in-theory (e/d (faithful-direct-event-result faithful-formula-data-p)
                            (bx-names-reserved bx-ev-type bx-ev-namex bx-ev-symbol-class bx-ev-form
                             bx-names bx-programp bx-all-program-p
                             bx-some-program-p bx-constrained-p
                             bx-all-constrained-p bx-some-constrained-p
                             bx-program-defs bx-define-items bx-add-candidates
                             bx-stobj-items fgetprop bx-conjuncts
                             bx-mentions-some constraint-info bx-choose-items
                             bx-constrain-items bx-package-items
                             bx-reserve-items bx-names-with-content))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-fact-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (member-equal (car line) '("theorem" "axiom"))
                   origin)
              (faithful-formula-data-p (cadr line) wrld)))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  (:instance faithful-fact-of-event
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

(defthm faithful-theorem-statement
  (implies
   (and (equal (car line) "theorem")
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-formula-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-fact-of-origin (lo 0))
                 faithful-fact-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines)
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-axiom-statement
  (implies
   (and (equal (car line) "axiom")
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-formula-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-fact-of-origin (lo 0))
                 faithful-fact-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines)
           :do-not-induct t))
  :rule-classes nil)
