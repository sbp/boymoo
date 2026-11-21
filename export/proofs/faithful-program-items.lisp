(in-package "ACL2")

(include-book "faithful-program-data")

; Event items tagged as program text are definitions. A definition may
; also be tagged as a statement when it has a meaning in the logic.

(defun faithful-program-items-p (items translations wrld bodies-p)
  (if (endp items)
      t
    (let* ((item (car items))
           (tag (car item))
           (word (cadr item)))
      (and (or (not (eq tag :prog)) (equal word "define"))
           (or (not bodies-p)
               (not (and (member-eq tag '(:prog :stmt)) (equal word "define")))
               (faithful-program-definitions-p (cdr (caddr item)) translations wrld))
           (faithful-program-items-p (cdr items) translations wrld bodies-p)))))

(defthm faithful-program-line-of-items
  (implies (and (faithful-program-items-p items translations wrld bodies-p)
                (member-equal (cons key line) items)
                (or (eq key :prog)
                    (and (eq key :stmt) (equal (car line) "define"))))
           (and (equal (car line) "define")
                (or (not bodies-p)
                    (faithful-program-definitions-p (cdr (cadr line)) translations wrld))))
  :hints (("Goal" :induct (faithful-program-items-p items translations wrld bodies-p)
           :in-theory (disable faithful-program-definitions-p)))
  :rule-classes nil)

(local
 (defthm faithful-program-items-of-append
   (equal (faithful-program-items-p (append a b) translations wrld bodies-p)
          (and (faithful-program-items-p a translations wrld bodies-p)
               (faithful-program-items-p b translations wrld bodies-p)))
   :hints (("Goal" :in-theory (disable faithful-program-definitions-p)))))

(local
 (defthm faithful-program-items-of-revappend
   (equal (faithful-program-items-p (revappend a b) translations wrld bodies-p)
          (and (faithful-program-items-p a translations wrld bodies-p)
               (faithful-program-items-p b translations wrld bodies-p)))
   :hints (("Goal" :induct (revappend a b)
            :in-theory (disable faithful-program-definitions-p)))))

; Notes do not supply a definition in either list.

(local
 (defthm faithful-program-body-note
   (and (not (equal (car (mv-nth 1 (bx-program-body fn form translations wrld))) :prog))
        (not (equal (car (mv-nth 1 (bx-program-body fn form translations wrld))) :stmt)))
   :hints (("Goal" :in-theory (disable bx-defun-forms fgetprop)))))

(local
 (defthm faithful-program-defs-notes-valid
   (implies (and (not (stringp notes))
                 (faithful-program-items-p notes translations wrld bodies-p))
            (faithful-program-items-p
             (mv-nth 1 (bx-program-defs fns form translations wrld defs notes))
             translations wrld bodies-p))
   :hints (("Goal" :induct (bx-program-defs fns form translations wrld defs notes)
            :in-theory (disable bx-program-body bx-exec formals
                                faithful-program-definitions-p)))))

(local
 (defthm faithful-constraint-candidate-notes-valid
   (implies (and (not (stringp notes))
                 (faithful-program-items-p notes translations wrld bodies-p))
            (faithful-program-items-p
             (mv-nth 2 (bx-candidate-terms cands stored owner wrld formulas covered notes))
             translations wrld bodies-p))
   :hints (("Goal"
            :induct (bx-candidate-terms cands stored owner wrld formulas covered notes)
            :in-theory (disable bx-equation-in bx-conjuncts union-equal
                                faithful-program-definitions-p)))))

(local
 (defthm faithful-uncovered-notes-valid
   (implies (and (not (stringp notes))
                 (faithful-program-items-p notes translations wrld bodies-p))
            (faithful-program-items-p
             (mv-nth 1 (bx-uncovered stored covered owner position wrld formulas notes))
             translations wrld bodies-p))
   :hints (("Goal"
            :induct (bx-uncovered stored covered owner position wrld formulas notes)
            :in-theory (disable bx-formula-name
                                faithful-program-definitions-p)))))

(local
 (defthm faithful-named-formula-notes-valid
   (faithful-program-items-p (mv-nth 1 (bx-name-formulas stored cands owner wrld))
                             translations wrld bodies-p)
   :hints (("Goal" :in-theory (disable bx-candidate-terms bx-uncovered)))))

; Each constructor with no definitions contributes only statements of
; other kinds, or notes.

(local
 (defthm faithful-items-of-bx-reserve-items
   (faithful-program-items-p (bx-reserve-items names wrld) translations wrld bodies-p)
   :hints (("Goal" :in-theory (disable bx-reserve-kind-p)))))

(local
 (defthm faithful-items-of-bx-choose-items
   (faithful-program-items-p (bx-choose-items fn wrld) translations wrld bodies-p)
   :hints (("Goal" :in-theory (disable bx-beta bx-choose-parts bx-choose-axiom
                                       formals fgetprop)))))

(local
 (defthm faithful-items-of-bx-package-items
   (faithful-program-items-p (bx-package-items name form wrld)
                             translations wrld bodies-p)
   :hints (("Goal" :in-theory (disable global-val fgetprop)))))

(local
 (defthm faithful-items-of-bx-constrain-items
   (faithful-program-items-p (faithful-direct-constrain-items names owner pending wrld)
                             translations wrld bodies-p)
   :hints (("Goal" :in-theory (e/d (faithful-direct-constrain-items)
                            (bx-name-formulas bx-candidate-formulas
                                       bx-arities bx-sort-by-event
                                       constraint-info fgetprop
                             faithful-formula-pending bx-formula-cands bx-later-items))))))

; Logical definitions use the stored bodies. Reordering an object's
; defined functions preserves their symbol class.

(local
 (defthm faithful-items-of-bx-define-items
   (implies (or (not bodies-p)
                (and (plist-worldp-with-formals wrld)
                     (faithful-nonprogram-fns-p fns wrld)))
            (faithful-program-items-p (bx-define-items fns wrld)
                                      translations wrld bodies-p))
   :hints (("Goal" :in-theory (disable bx-defs bx-rulers bx-same-rulers
                                       faithful-program-definitions-p
                                       plist-worldp-with-formals)))))

(local
 (defthm faithful-nonprogram-of-append
   (equal (faithful-nonprogram-fns-p (append a b) wrld)
          (and (faithful-nonprogram-fns-p a wrld)
               (faithful-nonprogram-fns-p b wrld)))))

(local
 (defthm faithful-nonprogram-of-revappend
   (equal (faithful-nonprogram-fns-p (revappend a b) wrld)
          (and (faithful-nonprogram-fns-p a wrld)
               (faithful-nonprogram-fns-p b wrld)))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm faithful-nonprogram-of-set-difference
   (implies (faithful-nonprogram-fns-p a wrld)
            (faithful-nonprogram-fns-p (set-difference-eq a b) wrld))))

(local
 (defthm faithful-nonprogram-of-bx-ready
   (implies (faithful-nonprogram-fns-p todo wrld)
            (faithful-nonprogram-fns-p (bx-ready todo placed wrld) wrld))
   :hints (("Goal" :in-theory (disable all-fnnames1 fgetprop)))))

(local
 (defthm faithful-nonprogram-of-bx-local-order
   (implies (and (not (stringp acc))
                 (faithful-nonprogram-fns-p todo wrld)
                 (faithful-nonprogram-fns-p acc wrld))
            (faithful-nonprogram-fns-p (bx-local-order todo placed acc wrld fuel)
                                       wrld))
   :hints (("Goal"
            :induct (bx-local-order todo placed acc wrld fuel)
            :in-theory (disable bx-ready set-difference-equal)))))

(local
 (defthm faithful-empty-nonprogram-fns
   (faithful-nonprogram-fns-p nil wrld)
   :hints (("Goal" :expand ((faithful-nonprogram-fns-p nil wrld))))))

(local
 (defthm faithful-items-of-bx-stobj-define-items
   (implies (or (not bodies-p)
                (and (plist-worldp-with-formals wrld)
                     (faithful-nonprogram-fns-p fns wrld)))
            (faithful-program-items-p (bx-stobj-define-items fns wrld)
                                      translations wrld bodies-p))
   :hints (("Goal" :in-theory (disable bx-define-items plist-worldp-with-formals)))))

(local
 (defthm faithful-items-of-bx-stobj-items
   (implies (and (not (stringp acc))
                 (faithful-program-items-p acc translations wrld bodies-p)
                 (or (not bodies-p)
                     (and (plist-worldp-with-formals wrld)
                          (faithful-nonprogram-fns-p fns-acc wrld)
                          (faithful-stobj-program-names-p names wrld))))
            (faithful-program-items-p (bx-stobj-items names defined fns-acc wrld acc)
                                      translations wrld bodies-p))
   :hints (("Goal"
            :induct (bx-stobj-items names defined fns-acc wrld acc)
            :in-theory (e/d (faithful-program-definition-p faithful-supplied-program-body)
                            (bx-stobj-define-items bx-local-order hons-get
                             bx-reserve-kind-p bx-exec formals fgetprop
                             plist-worldp-with-formals))))))

; Transfer the shape and body properties through the event dispatch.

(defthm faithful-program-items-of-event
  (implies (or (not bodies-p)
               (and (plist-worldp-with-formals wrld)
                    (or (not (member-eq (bx-ev-type ev) '(defstobj defabsstobj)))
                        (faithful-stobj-program-names-p (bx-names (bx-ev-namex ev))
                                                        wrld))))
           (faithful-program-items-p
            (mv-nth 0 (faithful-direct-event ev encl pending defined translations wrld))
            translations wrld bodies-p))
  :hints (("Goal"
           :use ((:instance faithful-bx-some-program-agrees
                            (fns (bx-names (bx-ev-namex ev)))))
           :in-theory (e/d (faithful-direct-event-result)
                            (bx-ev-type bx-ev-namex bx-ev-symbol-class bx-ev-form
                               bx-names bx-all-program-p bx-some-program-p bx-programp
                               bx-constrained-p bx-all-constrained-p bx-some-constrained-p
                               bx-program-defs bx-define-items bx-add-candidates
                               bx-stobj-items bx-conjuncts bx-mentions-some
                               bx-choose-items bx-constrain-items bx-package-items
                               bx-reserve-items bx-names-with-content constraint-info
                               fgetprop plist-worldp-with-formals
                               faithful-program-definitions-p faithful-stobj-program-names-p
                               faithful-nonprogram-fns-p faithful-bx-some-program-agrees
                             bx-names-reserved))
           :do-not-induct t)))
