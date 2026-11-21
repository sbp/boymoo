(in-package "ACL2")

(include-book "faithful-world")

; ACL2 records imports in its known package table. It also adds an
; imports axiom for an openly declared package.

(defund faithful-package-entry (name wrld)
  (find-package-entry
   name (getprop 'known-package-alist 'global-value nil 'current-acl2-world wrld)))

(defund faithful-known-packages-p (wrld)
  (not (eq (getprop 'known-package-alist 'global-value :absent
                     'current-acl2-world wrld)
           :absent)))

(defund faithful-package-axiom (name wrld)
  (getprop (intern-in-package-of-symbol (concatenate 'string name "-PACKAGE")
                                        'acl2::x)
           'theorem nil 'current-acl2-world wrld))

(defund faithful-imports-axiom (name imports)
  (list 'equal (list 'pkg-imports (list 'quote name)) (list 'quote imports)))

(defun faithful-imports-axiom-p (name term)
  (case-match term
    (('equal ('pkg-imports ('quote !name)) ('quote &)) t)
    (& nil)))

(defun faithful-package-axiom-agrees-p (entry wrld)
  (let* ((name (package-entry-name entry))
         (axiom (faithful-package-axiom name wrld)))
    (or (package-entry-hidden-p entry)
        (equal axiom (faithful-imports-axiom name (package-entry-imports entry)))
        (and (equal name "COMMON-LISP")
             (not (faithful-imports-axiom-p name axiom))))))

(defun faithful-package-axioms-agree-p (entries wrld)
  (if (endp entries)
      t
    (and (faithful-package-axiom-agrees-p (car entries) wrld)
         (faithful-package-axioms-agree-p (cdr entries) wrld))))

(defund faithful-package-world-p (wrld)
  (and (faithful-known-packages-p wrld)
       (faithful-package-axioms-agree-p
        (getprop 'known-package-alist 'global-value nil 'current-acl2-world wrld)
        wrld)))

(defund faithful-package-data-p (args wrld)
  (let* ((name (car args))
         (entry (faithful-package-entry name wrld))
         (imports (package-entry-imports entry)))
    (and entry
         (not (package-entry-hidden-p entry))
         (equal args (list name imports))
         (or (equal name "COMMON-LISP")
             (equal (faithful-package-axiom name wrld)
                    (faithful-imports-axiom name imports))))))

; ACL2 preserves a hidden declaration in its event landmark even after
; an open declaration reveals the package.

(defund faithful-hidden-flag-p (form)
  (and (true-listp form)
       (equal (len form) 6)
       (eq (car (last form)) t)))

(defund faithful-hidden-declaration-p (name event)
  (and (eq (access-event-tuple-type event) 'defpkg)
       (equal name (car (faithful-event-names event)))
       (faithful-hidden-flag-p (access-event-tuple-form event))))

(defund faithful-hidden-declaration-in-world-p (name triples)
  (if (endp triples)
      nil
    (or (and (eq (caar triples) 'event-landmark)
             (eq (cadar triples) 'global-value)
             (faithful-hidden-declaration-p name (cddar triples)))
        (faithful-hidden-declaration-in-world-p name (cdr triples)))))

(defund faithful-hidden-package-data-p (args wrld)
  (let* ((name (car args))
         (entry (faithful-package-entry name wrld))
         (imports (package-entry-imports entry)))
    (and entry
         (equal args (list name imports))
         (or (package-entry-hidden-p entry)
             (faithful-hidden-declaration-in-world-p name wrld)))))

; The known package table and the imports axiom supply the data in the
; open case. For a hidden declaration only the table supplies imports.

(local
 (defthm faithful-package-entry-of-global-val
   (implies (faithful-known-packages-p wrld)
            (equal (find-package-entry name (global-val 'known-package-alist wrld))
                   (faithful-package-entry name wrld)))
   :hints (("Goal"
            :induct (fgetprop 'known-package-alist 'global-value nil wrld)
            :in-theory (enable faithful-known-packages-p faithful-package-entry
                               global-val fgetprop)))))

(local
 (defthm faithful-package-world-has-known-packages
   (implies (faithful-package-world-p wrld)
            (faithful-known-packages-p wrld))
   :hints (("Goal" :in-theory (enable faithful-package-world-p)))
   :rule-classes :forward-chaining))

(local
 (defthm faithful-package-axiom-for-entry
   (implies (and (faithful-package-axioms-agree-p entries wrld)
                 (find-package-entry name entries))
            (faithful-package-axiom-agrees-p (find-package-entry name entries)
                                            wrld))
   :hints (("Goal" :in-theory (disable faithful-package-axiom-agrees-p)))))

(local
 (defthm faithful-package-axiom-in-world
   (implies (and (faithful-package-world-p wrld)
                 (faithful-package-entry name wrld))
            (faithful-package-axiom-agrees-p (faithful-package-entry name wrld)
                                            wrld))
   :hints (("Goal"
            :in-theory (e/d (faithful-package-world-p faithful-package-entry)
                            (faithful-package-axiom-agrees-p fgetprop))))))

(local
 (defthm faithful-key-of-assoc-equal
   (implies (assoc-equal name entries)
            (equal (car (assoc-equal name entries)) name))))

(local
 (defthm faithful-name-of-package-entry
   (implies (faithful-package-entry name wrld)
            (equal (package-entry-name (faithful-package-entry name wrld)) name))
   :hints (("Goal" :in-theory (e/d (faithful-package-entry) (fgetprop))))))

(local
 (defthm faithful-hidden-declaration-in-landmark
   (implies (and (faithful-event-landmark-p event wrld)
                 (faithful-hidden-declaration-p name event))
            (faithful-hidden-declaration-in-world-p name wrld))
   :hints (("Goal" :induct (faithful-hidden-declaration-in-world-p name wrld)
            :in-theory (enable faithful-event-landmark-p
                               faithful-hidden-declaration-in-world-p)))))

(local
 (defthm faithful-package-data-of-items
   (implies (and (equal (car line) "package")
                 (faithful-package-world-p wrld)
                 (member-equal (cons :stmt line) (bx-package-items name form wrld)))
            (faithful-package-data-p (cadr line) wrld))
   :hints (("Goal"
            :use (faithful-package-axiom-in-world
                  faithful-name-of-package-entry)
            :in-theory (e/d (faithful-package-data-p faithful-package-axiom
                                                     faithful-imports-axiom)
                            (faithful-package-axiom-in-world fgetprop global-val
                             faithful-name-of-package-entry))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-hidden-package-data-of-items
   (implies (and (equal (car line) "hidden-package")
                 (faithful-known-packages-p wrld)
                 (or (not (faithful-hidden-flag-p form))
                     (faithful-hidden-declaration-in-world-p name wrld))
                 (member-equal (cons :stmt line) (bx-package-items name form wrld)))
            (faithful-hidden-package-data-p (cadr line) wrld))
   :hints (("Goal"
            :in-theory (e/d (faithful-hidden-package-data-p faithful-hidden-flag-p)
                            (fgetprop global-val))
            :do-not-induct t))
   :rule-classes nil))

; Trace a package statement to its declaration. The hidden flag is read
; from the originating event as well as from the current table.

(local
 (defthm faithful-package-items-of-event
   (implies (and (member-equal (car line) '("package" "hidden-package"))
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                          translations wrld))))
            (and (eq (access-event-tuple-type ev) 'defpkg)
                 (member-equal (cons :stmt line)
                               (bx-package-items (car (faithful-event-names ev))
                                                 (access-event-tuple-form ev)
                                                 wrld))))
   :hints (("Goal"
            :use (faithful-statement-word-of-event
                  (:instance faithful-event-type-reader (event ev))
                  (:instance faithful-event-name-reader (event ev))
                  (:instance faithful-event-form-reader (event ev)))
            :in-theory (e/d (faithful-direct-event-result)
                            (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                                access-event-tuple-type access-event-tuple-form
                                faithful-event-names
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
 (defthm faithful-package-items-of-origin
   (let* ((origin (faithful-statement-origin line lo hi translations wrld))
          (event (car origin)))
     (implies (and (member-equal (car line) '("package" "hidden-package"))
                   origin)
              (and (eq (access-event-tuple-type event) 'defpkg)
                   (faithful-event-landmark-p event wrld)
                   (member-equal
                    (cons :stmt line)
                    (bx-package-items (car (faithful-event-names event))
                                      (access-event-tuple-form event) wrld)))))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  faithful-landmark-of-statement-origin
                  (:instance faithful-package-items-of-event
                             (ev (car (faithful-statement-origin
                                       line lo hi translations wrld)))
                             (encl (cadr (faithful-statement-origin
                                         line lo hi translations wrld)))
                             (pending (caddr (faithful-statement-origin
                                             line lo hi translations wrld)))
                             (defined (cadddr (faithful-statement-origin
                                               line lo hi translations wrld)))))
            :in-theory (disable bx-event-items bx-package-items faithful-event-names
                                access-event-tuple-type access-event-tuple-form)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-package-of-origin
   (implies (and (equal (car line) "package")
                 (faithful-package-world-p wrld)
                 (faithful-statement-origin line lo hi translations wrld))
            (faithful-package-data-p (cadr line) wrld))
   :hints (("Goal"
            :use (faithful-package-items-of-origin
                  (:instance faithful-package-data-of-items
                             (name (car (faithful-event-names
                                         (car (faithful-statement-origin
                                               line lo hi translations wrld)))))
                             (form (access-event-tuple-form
                                    (car (faithful-statement-origin
                                          line lo hi translations wrld))))))
            :in-theory (disable bx-package-items faithful-event-names
                                access-event-tuple-type access-event-tuple-form)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-hidden-package-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (equal (car line) "hidden-package")
                   (faithful-known-packages-p wrld)
                   origin)
              (faithful-hidden-package-data-p (cadr line) wrld)))
   :hints (("Goal"
            :use (faithful-package-items-of-origin
                  (:instance faithful-hidden-package-data-of-items
                             (name (car (faithful-event-names
                                         (car (faithful-statement-origin
                                               line lo hi translations wrld)))))
                             (form (access-event-tuple-form
                                    (car (faithful-statement-origin
                                          line lo hi translations wrld))))))
            :in-theory (e/d (faithful-hidden-declaration-p)
                            (bx-package-items faithful-event-names
                             access-event-tuple-type access-event-tuple-form))
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-package-statement
  (implies
   (and (equal (car line) "package")
        (faithful-package-world-p wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-package-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-package-of-origin (lo 0))
                 faithful-package-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines)
           :do-not-induct t))
  :rule-classes nil)

(defthm faithful-hidden-package-statement
  (implies
   (and (equal (car line) "hidden-package")
        (faithful-known-packages-p wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-hidden-package-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-hidden-package-of-origin (lo 0))
                 faithful-hidden-package-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines)
           :do-not-induct t))
  :rule-classes nil)
