(in-package "ACL2")

(include-book "faithful-origin")

; Identify the statement words that each event can produce. The lemma about
; membership lets each data proof consider only the events for its word.

(defund faithful-statement-words-p (items words)
  (if (endp items)
      t
    (and (or (not (eq (caar items) :stmt))
             (member-equal (cadar items) words))
         (faithful-statement-words-p (cdr items) words))))

(local (in-theory (enable faithful-statement-words-p)))

(defthm faithful-statement-word-of-member
  (implies (and (faithful-statement-words-p items words)
                (member-equal (cons :stmt line) items))
           (member-equal (car line) words))
  :hints (("Goal" :induct (faithful-statement-words-p items words)))
  :rule-classes nil)

(local
 (defthm faithful-statement-words-of-append
   (equal (faithful-statement-words-p (append a b) words)
          (and (faithful-statement-words-p a words)
               (faithful-statement-words-p b words)))))

(local
 (defthm faithful-statement-words-of-revappend
   (equal (faithful-statement-words-p (revappend a b) words)
          (and (faithful-statement-words-p a words)
               (faithful-statement-words-p b words)))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm faithful-statement-words-of-reverse
   (implies (not (stringp a))
            (equal (faithful-statement-words-p (reverse a) words)
                   (faithful-statement-words-p a words)))))

; The auxiliary results of these constructors are lists of notes.

(local
 (defthm faithful-program-body-note-is-not-statement
   (not (equal (car (mv-nth 1 (bx-program-body fn form translations wrld)))
               :stmt))
   :hints (("Goal" :in-theory (disable bx-defun-forms)))))

(local
 (defthm faithful-program-defs-notes-have-no-statement
   (implies (and (not (stringp notes))
                 (faithful-statement-words-p notes words))
            (faithful-statement-words-p
             (mv-nth 1 (bx-program-defs fns form translations wrld defs notes))
             words))
   :hints (("Goal"
            :induct (bx-program-defs fns form translations wrld defs notes)
            :in-theory (disable bx-program-body bx-exec)))))

(defthm faithful-no-statement-in-program-defs-notes
  (not (member-equal (cons :stmt line)
                     (mv-nth 1 (bx-program-defs fns form translations wrld defs nil))))
  :hints (("Goal"
           :use ((:instance faithful-program-defs-notes-have-no-statement
                            (notes nil) (words nil))
                 (:instance faithful-statement-word-of-member
                            (items (mv-nth 1 (bx-program-defs
                                              fns form translations wrld defs nil)))
                            (words nil)))
           :in-theory (disable bx-program-defs faithful-statement-words-p))))

(local
 (defthm faithful-candidate-terms-notes-have-no-statement
   (implies (and (not (stringp notes))
                 (faithful-statement-words-p notes words))
            (faithful-statement-words-p
             (mv-nth 2 (bx-candidate-terms cands lst c wrld formulas covered notes))
             words))
   :hints (("Goal"
            :induct (bx-candidate-terms cands lst c wrld formulas covered notes)
            :in-theory (disable bx-equation-in bx-conjuncts union-equal)))))

(local
 (defthm faithful-uncovered-notes-have-no-statement
   (implies (and (not (stringp notes))
                 (faithful-statement-words-p notes words))
            (faithful-statement-words-p
             (mv-nth 1 (bx-uncovered lst covered c i wrld formulas notes))
             words))
   :hints (("Goal"
            :induct (bx-uncovered lst covered c i wrld formulas notes)
            :in-theory (disable bx-formula-name)))))

(defthm faithful-name-formulas-notes-have-no-statement
  (faithful-statement-words-p (mv-nth 1 (bx-name-formulas lst cands c wrld))
                              words)
  :hints (("Goal" :in-theory (disable bx-candidate-terms bx-uncovered))))

; A constructor produces only its designated kinds of statements.

(local
 (defthm faithful-define-items-words
   (implies (member-equal "define" words)
            (faithful-statement-words-p (bx-define-items fns wrld) words))
   :hints (("Goal" :in-theory (disable bx-defs bx-rulers bx-same-rulers)))))

(local
 (defthm faithful-stobj-define-items-words
   (implies (member-equal "define" words)
            (faithful-statement-words-p (bx-stobj-define-items fns wrld) words))
   :hints (("Goal" :in-theory (disable bx-define-items)))))

(local
 (defthm faithful-stobj-items-words
   (implies (and (not (stringp acc))
                 (member-equal "define" words)
                 (member-equal "reserve" words)
                 (faithful-statement-words-p acc words))
            (faithful-statement-words-p
             (bx-stobj-items names defined fns-acc wrld acc) words))
   :hints (("Goal"
            :induct (bx-stobj-items names defined fns-acc wrld acc)
            :in-theory (disable bx-stobj-define-items bx-exec
                                bx-reserve-kind-p bx-function-p bx-programp
                                bx-local-order hons-get formals fgetprop)))))

(local
 (defthm faithful-reserve-items-words
   (implies (member-equal "reserve" words)
            (faithful-statement-words-p (bx-reserve-items names wrld) words))
   :hints (("Goal" :in-theory (disable bx-reserve-kind-p)))))

(local
 (defthm faithful-package-items-words
   (implies (and (member-equal "package" words)
                 (member-equal "hidden-package" words))
            (faithful-statement-words-p (bx-package-items name form wrld) words))
   :hints (("Goal" :in-theory (disable fgetprop global-val)))))

(local
 (defthm faithful-choose-items-words
   (implies (member-equal "choose" words)
            (faithful-statement-words-p (bx-choose-items fn wrld) words))
   :hints (("Goal" :in-theory (disable bx-choose-parts bx-choose-axiom bx-beta
                                       formals fgetprop)))))

(local
 (defthm faithful-constrain-items-words
   (implies (member-equal "constrain" words)
            (faithful-statement-words-p (faithful-direct-constrain-items names c pending wrld)
                                        words))
   :hints (("Goal" :in-theory (e/d (faithful-direct-constrain-items)
                            (bx-arities bx-candidate-formulas
                                       bx-sort-by-event bx-name-formulas
                                       constraint-info fgetprop faithful-formula-pending
                                       bx-formula-cands bx-later-items))))))

(defun faithful-event-statement-words (type)
  (case type
    ((defun defuns) '("define"))
    (defthm '("theorem"))
    (defaxiom '("axiom"))
    (defpkg '("package" "hidden-package"))
    (defchoose '("choose"))
    (encapsulate '("constrain"))
    ((defconst defmacro deflabel deftheory) '("reserve"))
    ((defstobj defabsstobj) '("define" "reserve"))
    (otherwise nil)))

(local
 (defthm faithful-event-items-words
   (faithful-statement-words-p
    (mv-nth 0 (faithful-direct-event ev encl pending defined translations wrld))
    (faithful-event-statement-words (bx-ev-type ev)))
   :hints (("Goal"
            :in-theory (e/d (faithful-direct-event-result)
                            (bx-ev-type bx-ev-namex bx-ev-symbol-class bx-ev-form
                                bx-names bx-programp bx-all-program-p
                                bx-some-program-p bx-constrained-p
                                bx-all-constrained-p bx-some-constrained-p
                                bx-program-defs bx-define-items bx-add-candidates
                                bx-constrainer bx-definition-candidates
                                bx-formula-name bx-conjuncts bx-mentions-some
                                bx-names-with-content bx-package-items
                                bx-choose-items bx-constrain-items bx-reserve-items
                                bx-stobj-items constraint-info fgetprop bx-names-reserved))))))

(defthm faithful-statement-word-of-event
  (implies (member-equal (cons :stmt line)
                         (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                    translations wrld)))
           (member-equal (car line)
                         (faithful-event-statement-words (bx-ev-type ev))))
  :hints (("Goal"
           :use (faithful-event-items-words
                 (:instance faithful-statement-word-of-member
                            (items (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                             translations wrld)))
                            (words (faithful-event-statement-words (bx-ev-type ev)))))
           :in-theory (disable faithful-event-items-words bx-event-items
                               bx-ev-type faithful-event-statement-words
                               faithful-statement-words-p)))
  :rule-classes nil)
