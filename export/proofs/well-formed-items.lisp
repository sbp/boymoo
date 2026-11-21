(in-package "ACL2")

(include-book "well-formed-world")

(set-verify-guards-eagerness 0)

;;; Each emitted item carries a statement, a program line or a note.
;;; Notes are kept in a different output and need no statement shape.

(defun wf-items-p (items)
  (if (consp items)
      (and (case (caar items)
             (:stmt (wf-statement-line-p (cdar items)))
             (:prog (wf-program-line-p (cdar items)))
             (:note t)
             (otherwise nil))
           (wf-items-p (cdr items)))
    (null items)))

(local
 (in-theory (disable fgetprop formals global-val constraint-info wf-world-property-shapes-p
                     wf-world-properties-p wf-event-data-p wf-term-p
                     wf-term-list-p wf-exec-input-p wf-property-details-p)))

(defthm wf-items-p-of-append
  (implies (and (wf-items-p a) (wf-items-p b))
           (wf-items-p (append a b))))

(defthm wf-items-p-of-revappend
  (implies (and (wf-items-p a) (wf-items-p b))
           (wf-items-p (revappend a b))))

(defthm wf-items-p-of-reverse
  (implies (wf-items-p a) (wf-items-p (reverse a))))

;;; Definitions read both from world properties and from translations.

(local
 (defthm wf-definition-list-p-of-revappend
   (implies (and (wf-definition-list-p a) (wf-definition-list-p b))
            (wf-definition-list-p (revappend a b)))))

(local
 (defthm wf-definition-list-p-of-reverse
   (implies (wf-definition-list-p a) (wf-definition-list-p (reverse a)))))

(local
 (defthm wf-definition-list-p-of-bx-defs
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-ground-functions-p fns wrld))
            (wf-definition-list-p (bx-defs fns wrld)))
   :hints (("Goal" :induct (bx-defs fns wrld)))))

(local
 (defthm wf-bx-defs-nonempty
   (equal (consp (bx-defs fns wrld)) (consp fns))))

(local
 (defthm wf-bx-define-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-ground-functions-p fns wrld)
                 (consp fns))
            (wf-items-p (bx-define-items fns wrld)))
   :hints (("Goal" :in-theory (disable bx-defs bx-rulers)))))

(local
 (defthm wf-translated-program-body
   (implies (and (wf-translations-p translations)
                 (eq (cadr (assoc-equal fn translations)) :ok)
                 (cddr (assoc-equal fn translations)))
            (and (wf-term-p (cddr (assoc-equal fn translations)))
                 (wf-exec-input-p (cddr (assoc-equal fn translations)))))
   :hints (("Goal" :induct (assoc-equal fn translations)))))

(local
 (defthm wf-term-p-of-bx-program-body
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-translations-p translations)
                 (car (bx-program-body fn form translations wrld)))
            (and (wf-term-p (car (bx-program-body fn form translations wrld)))
                 (wf-exec-input-p (car (bx-program-body fn form translations wrld)))))))

(local
 (defthm wf-program-formals
   (implies (and (wf-world-properties-p wrld)
                 (car (bx-program-body fn form translations wrld)))
            (arglistp (formals fn wrld)))
   :rule-classes nil))

(local
 (defthm wf-note-of-bx-program-body
   (implies (mv-nth 1 (bx-program-body fn form translations wrld))
            (equal (car (mv-nth 1 (bx-program-body fn form translations wrld)))
                   :note))))

(local
 (defthm wf-bx-program-defs
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-translations-p translations)
                 (wf-function-name-list-p names)
                 (wf-definition-list-p defs)
                 (wf-items-p notes))
            (and (wf-definition-list-p
                  (car (bx-program-defs names form translations wrld defs notes)))
                 (wf-items-p
                  (mv-nth 1 (bx-program-defs names form translations wrld defs notes)))))
   :hints (("Goal" :induct (bx-program-defs names form translations wrld defs notes)
            :in-theory (disable bx-exec bx-program-body))
           ("Subgoal *1/2"
            :use ((:instance wf-program-formals (fn (car names))))))))

;;; The order chosen for the functions of a single-threaded object
;;; preserves the names and the existence of their stored bodies.

(local
 (defthm wf-ground-functions-p-of-append
   (implies (and (wf-ground-functions-p a wrld) (wf-ground-functions-p b wrld))
            (wf-ground-functions-p (append a b) wrld))
   :hints (("Goal" :induct (append a b)))))

(local
 (defthm wf-ground-functions-p-of-revappend
   (implies (and (wf-ground-functions-p a wrld) (wf-ground-functions-p b wrld))
            (wf-ground-functions-p (revappend a b) wrld))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm wf-true-listp-when-function-names
   (implies (wf-function-name-list-p xs) (true-listp xs))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm wf-ground-functions-p-of-reverse
   (implies (wf-ground-functions-p a wrld)
            (wf-ground-functions-p (reverse a) wrld))
   :hints (("Goal" :use ((:instance wf-ground-functions-p-of-revappend (b nil)))
            :in-theory (disable wf-ground-functions-p-of-revappend)))))

(local
 (defthm wf-ground-functions-p-of-nil
   (wf-ground-functions-p nil wrld)))

(local
 (defthm wf-ground-functions-p-of-set-difference
   (implies (wf-ground-functions-p a wrld)
            (wf-ground-functions-p (set-difference-equal a b) wrld))
   :hints (("Goal" :induct (set-difference-equal a b)))))

(local
 (defthm wf-ground-functions-p-of-bx-ready
   (implies (wf-ground-functions-p names wrld)
            (wf-ground-functions-p (bx-ready names placed wrld) wrld))
   :hints (("Goal" :induct (bx-ready names placed wrld)))))

(local
 (defthm wf-ground-functions-p-of-bx-local-order
   (implies (and (wf-ground-functions-p names wrld)
                 (wf-ground-functions-p acc wrld))
            (wf-ground-functions-p (bx-local-order names placed acc wrld fuel) wrld))
   :hints (("Goal" :induct (bx-local-order names placed acc wrld fuel)
            :in-theory (disable bx-ready wf-ground-functions-p reverse)))))

(local
 (defthm wf-bx-stobj-define-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-ground-functions-p fns wrld))
            (wf-items-p (bx-stobj-define-items fns wrld)))
   :hints (("Goal" :induct (bx-stobj-define-items fns wrld)
            :in-theory (disable bx-define-items)))))

(local
 (defthm wf-bx-stobj-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-stobj-event-data-p names wrld)
                 (wf-ground-functions-p fns-acc wrld)
                 (wf-items-p acc))
            (wf-items-p (bx-stobj-items names defined fns-acc wrld acc)))
   :hints (("Goal" :induct (bx-stobj-items names defined fns-acc wrld acc)
            :in-theory (disable bx-function-p bx-programp bx-reserve-kind-p
                                bx-local-order bx-stobj-define-items bx-exec)))))

(local
 (defthm wf-bx-reserve-items
   (implies (wf-reserve-names-p names wrld)
            (wf-items-p (bx-reserve-items names wrld)))
   :hints (("Goal" :induct (bx-reserve-items names wrld)
            :in-theory (disable bx-reserve-kind-p)))))

;;; Constraints use formulas in a stored list or formulas supplied by
;;; events in the encapsulate. Candidates record a formula or the name
;;; of a function whose stored body supplies an equation. A pending
;;; list may also contain the items held to follow that constraint.

(defun wf-candidates-p (cands wrld with-items)
  (if (consp cands)
      (let ((cand (car cands)))
        (and (case (cadr cand)
               (:formula (and (wf-name-p (car cand))
                              (wf-term-p (caddr cand))))
               (:definition (and (wf-name-p (car cand))
                                 (wf-ground-functions-p (list (caddr cand)) wrld)))
               (:after (and with-items (null (car cand)) (wf-items-p (caddr cand))))
               (otherwise nil))
             (wf-candidates-p (cdr cands) wrld with-items)))
    (null cands)))

(defun wf-pending-p (pending wrld)
  (if (consp pending)
      (and (wf-candidates-p (cdar pending) wrld t)
           (wf-pending-p (cdr pending) wrld))
    (null pending)))

(local
 (defthm wf-candidates-p-of-append
   (implies (and (wf-candidates-p a wrld with-items)
                 (wf-candidates-p b wrld with-items))
            (wf-candidates-p (append a b) wrld with-items))))

(local
 (defthm wf-candidates-p-of-assoc
   (implies (wf-pending-p pending wrld)
            (wf-candidates-p (cdr (assoc-equal c pending)) wrld t))
   :hints (("Goal" :induct (assoc-equal c pending)))))

(local
 (defthm wf-pending-p-of-put-assoc
   (implies (and (wf-pending-p pending wrld) (wf-candidates-p cands wrld t))
            (wf-pending-p (put-assoc-equal c cands pending) wrld))))

(local
 (defthm wf-pending-p-of-bx-add-candidates
   (implies (and (wf-pending-p pending wrld) (wf-candidates-p cands wrld t))
            (wf-pending-p (bx-add-candidates c cands pending) wrld))))

(local
 (defthm wf-formula-candidates
   (implies (wf-candidates-p cands wrld t)
            (wf-candidates-p (bx-formula-cands cands) wrld nil))
   :hints (("Goal" :induct (bx-formula-cands cands)))))

(local
 (defthm wf-later-items
   (implies (wf-candidates-p cands wrld t)
            (wf-items-p (bx-later-items cands)))
   :hints (("Goal" :induct (bx-later-items cands)))))

;;; Name search returns NIL at failure. Any name it supplies belongs to
;;; the source function's package and is unused in the world.

(defthm well-formed-fresh-constraint-name
  (let ((name (bx-fresh-name base i fn wrld fuel)))
    (and (wf-name-p name)
         (or (null name)
             (and (equal (symbol-package-name name) (symbol-package-name fn))
                  (not (bx-in-use-p name wrld))))))
  :hints (("Goal" :induct (bx-fresh-name base i fn wrld fuel)
           :in-theory (disable bx-in-use-p))))

(local
 (defthm wf-name-p-of-bx-formula-name
   (wf-name-p (bx-formula-name fn word wrld))
   :hints (("Goal" :in-theory (disable bx-fresh-name wf-name-p)))))

(local
 (defthm wf-candidates-p-of-bx-definition-candidates
   (implies (wf-ground-functions-p names wrld)
            (wf-candidates-p (bx-definition-candidates names wrld) wrld with-items))
   :hints (("Goal" :induct (bx-definition-candidates names wrld)
            :in-theory (disable bx-fresh-name)))))

(local
 (defthm wf-name-list-p-of-set-difference
   (implies (wf-function-name-list-p a)
            (wf-function-name-list-p (set-difference-equal a b)))))

(local
 (defthm wf-name-list-p-of-append
   (implies (and (wf-function-name-list-p a) (wf-function-name-list-p b))
            (wf-function-name-list-p (append a b)))))

(local
 (defthm wf-name-list-p-of-bx-insert-by-event
   (implies (and (wf-function-name-p fn) (wf-function-name-list-p fns))
            (wf-function-name-list-p (bx-insert-by-event fn fns wrld)))))

(local
 (defthm wf-name-list-p-of-bx-sort-by-event
   (implies (wf-function-name-list-p fns)
            (wf-function-name-list-p (bx-sort-by-event fns wrld)))
   :hints (("Goal" :in-theory (disable bx-insert-by-event)))))

(local
 (defthm wf-arity-list-p-of-bx-arities
   (implies (wf-function-name-list-p fns)
            (wf-arity-list-p (bx-arities fns wrld)))))

(local
 (defthm wf-bx-arities-nonempty
   (equal (consp (bx-arities fns wrld)) (consp fns))))

(local
 (defthm wf-append-nonempty-when-first-nonempty
   (implies (consp a) (consp (append a b)))))

(local
 (defthm wf-named-formula-list-p-of-append
   (implies (and (wf-named-formula-list-p a) (wf-named-formula-list-p b))
            (wf-named-formula-list-p (append a b)))))

(local
 (defthm wf-named-formula-list-p-of-revappend
   (implies (and (wf-named-formula-list-p a) (wf-named-formula-list-p b))
            (wf-named-formula-list-p (revappend a b)))))

(local
 (defthm wf-named-formula-list-p-of-reverse
   (implies (wf-named-formula-list-p a)
            (wf-named-formula-list-p (reverse a)))))

(local
 (defthm wf-term-list-p-of-car-and-cdr
   (implies (and (wf-term-list-p xs) (consp xs))
            (and (wf-term-p (car xs)) (wf-term-list-p (cdr xs))))
   :hints (("Goal" :in-theory (enable wf-term-p wf-term-list-p)))))

(local
 (defthm wf-equation-in-p
   (implies (and (wf-term-list-p lst) (bx-equation-in fn lst wrld))
            (wf-term-p (bx-equation-in fn lst wrld)))
   :hints (("Goal" :induct (bx-equation-in fn lst wrld)))))

(local
 (defthm wf-bx-candidate-terms
   (implies (and (wf-candidates-p cands wrld nil)
                 (wf-term-list-p lst)
                 (wf-named-formula-list-p formulas)
                 (wf-items-p notes))
            (and (wf-named-formula-list-p
                  (car (bx-candidate-terms cands lst c wrld formulas covered notes)))
                 (wf-items-p
                  (mv-nth 2 (bx-candidate-terms cands lst c wrld formulas covered notes)))))
   :hints (("Goal" :induct (bx-candidate-terms cands lst c wrld formulas covered notes)
            :in-theory (disable bx-conjuncts bx-equation-in)))))

(local
 (defthm wf-bx-uncovered
   (implies (and (wf-term-list-p lst)
                 (wf-named-formula-list-p formulas)
                 (wf-items-p notes))
            (and (wf-named-formula-list-p
                  (car (bx-uncovered lst covered c i wrld formulas notes)))
                 (wf-items-p (mv-nth 1 (bx-uncovered lst covered c i wrld formulas notes)))))
   :hints (("Goal" :induct (bx-uncovered lst covered c i wrld formulas notes)
            :in-theory (disable bx-fresh-name)))))

(local
 (defthm wf-bx-name-formulas
   (implies (and (wf-term-list-p lst) (wf-candidates-p cands wrld nil))
            (and (wf-named-formula-list-p (car (bx-name-formulas lst cands c wrld)))
                 (wf-items-p (mv-nth 1 (bx-name-formulas lst cands c wrld)))))
   :hints (("Goal" :in-theory (disable bx-candidate-terms bx-uncovered)))))

(local
 (defthm wf-term-list-p-of-symbol-list
   (implies (arglistp xs) (wf-term-list-p xs))
   :hints (("Goal" :induct (symbol-listp xs)
            :in-theory (enable arglistp arglistp1 wf-term-p wf-term-list-p)))))

(local
 (defthm wf-bx-candidate-formulas
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-candidates-p cands wrld nil))
            (wf-named-formula-list-p (bx-candidate-formulas cands wrld)))
   :hints (("Goal" :induct (bx-candidate-formulas cands wrld)))))

;;; The constraint itself contributes exactly one item. An absent
;;; formula name produces a note, irrespective of the world.

(defthm constraint-statement-or-missing-name-note
  (let ((items (bx-constrain-stmt fns formulas wrld)))
    (if (member-eq nil (strip-cars formulas))
        (equal items
               (list (list :note
                           "constraint with a formula for which no unused name was found"
                           (append fns (remove-eq nil (strip-cars formulas))))))
      (and (consp items)
           (null (cdr items))
           (eq (caar items) :stmt)
           (equal (cadar items) "constrain"))))
  :rule-classes nil)

(defthm constraint-missing-name-note-names-introductions
  (implies (member-equal nil (strip-cars formulas))
           (iff (member-equal name (caddar (bx-constrain-stmt fns formulas wrld)))
                (or (member-equal name fns)
                    (and name (member-equal name (strip-cars formulas))))))
  :rule-classes nil)

(local
 (defthm wf-bx-constrain-stmt
   (implies (and (wf-function-name-list-p fns)
                 (consp fns)
                 (wf-named-formula-list-p formulas))
            (wf-items-p (bx-constrain-stmt fns formulas wrld)))
   :hints (("Goal" :in-theory (disable bx-arities)))))

(local
 (defthm wf-bx-constrain-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-function-name-list-p names)
                 (consp names)
                 (wf-constraint-owner-p c wrld)
                 (wf-pending-p pending wrld))
            (wf-items-p (bx-constrain-items names c pending wrld)))
   :hints (("Goal" :use ((:instance wf-later-items
                                   (cands (cdr (assoc-equal c pending)))))
            :do-not-induct t
            :in-theory (disable bx-arities bx-sort-by-event bx-name-formulas
                                bx-candidate-formulas bx-constrain-stmt
                                bx-formula-cands bx-later-items wf-later-items
                                unknown-constraints-p wf-constraint-owner-p)))))

;;; A package line comes from a known package. The imports can come
;;; from its axiom or its entry in ACL2's list of packages.

(local
 (defthm wf-known-package-association
   (implies (and (known-package-alistp packages)
                 (wf-package-alist-names-p packages)
                 (assoc-equal name packages))
            (and (wf-package-name-p name)
                 (symbol-listp (cadr (assoc-equal name packages)))))
   :hints (("Goal" :induct (assoc-equal name packages)
            :in-theory (disable wf-package-name-p)))))

(local
 (defthm wf-bx-package-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (getpropc 'known-package-alist 'global-value nil wrld))
            (wf-items-p (bx-package-items name form wrld)))
   :hints (("Goal" :use ((:instance wf-world-package-axiom
                                   (rule (intern-in-package-of-symbol
                                          (concatenate 'string name "-PACKAGE") 'acl2::x)))
                        (:instance wf-known-package-association
                                   (packages (getpropc 'known-package-alist
                                                       'global-value nil wrld))))
            :in-theory (disable wf-world-package-axiom
                                wf-known-package-association
                                wf-package-name-p assoc-equal)))))

;;; Choice checks its reconstruction before it emits a line. The
;;; recognition proof uses the shapes of the axiom and its formals.

(local
 (defthm wf-bx-choose-items-without-axiom
   (implies (null (getpropc fn 'defchoose-axiom nil wrld))
            (wf-items-p (bx-choose-items fn wrld)))))

(local
 (defthm wf-axiom-present-when-bound-found
   (implies (car (bx-choose-parts axiom fn wrld)) axiom)
   :rule-classes :forward-chaining))

(local
 (defthm wf-consp-of-nonempty-arglist
   (implies (and (arglistp xs) xs) (consp xs))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable arglistp arglistp1)))))

(local
 (defthm wf-choice-second-formals-of-bx-choose-parts
   (implies (wf-choice-second-formals-p fn axiom (formals fn wrld))
            (let ((free2 (mv-nth 2 (bx-choose-parts axiom fn wrld))))
              (or (null free2)
                  (and (arglistp free2) (equal (len free2) (len (formals fn wrld)))))))
   :hints (("Goal" :in-theory (disable bx-bound-one bx-bound-many)))))

(local
 (defthm wf-bx-choose-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-function-name-p fn)
                 (arglistp (formals fn wrld))
                 (wf-choice-second-formals-p
                  fn (getpropc fn 'defchoose-axiom nil wrld) (formals fn wrld)))
            (wf-items-p (bx-choose-items fn wrld)))
   :hints (("Goal" :use ((:instance wf-bx-choose-parts
                                   (axiom (getpropc fn 'defchoose-axiom nil wrld)))
                        (:instance wf-choice-second-formals-of-bx-choose-parts
                                   (axiom (getpropc fn 'defchoose-axiom nil wrld))))
            :in-theory (disable bx-beta bx-choose-axiom bx-choose-parts
                                bx-choose-literal
                                wf-bx-choose-parts wf-choice-second-formals-of-bx-choose-parts
                                wf-choice-second-formals-p)))))

;;; Event processing preserves the shapes of the lines and of the
;;; candidates kept for future constraints.

(local
 (defthm wf-names-of-encapsulate
   (implies (wf-encapsulate-data-p names wrld)
            (wf-function-name-list-p names))))

(local
 (defthm wf-names-when-not-all-constrained
   (implies (not (bx-all-constrained-p names wrld))
            (consp names))
   :rule-classes :forward-chaining))

(local
 (defthm wf-definition-list-p-when-nonempty
   (implies (and (wf-definition-list-p defs) defs) (consp defs))
   :rule-classes :forward-chaining))

(local
 (defthm wf-bx-event-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-translations-p translations)
                 (wf-event-data-p ev wrld)
                 (wf-pending-p pending wrld))
            (and (wf-items-p (car (bx-event-items ev encl pending defined
                                                      translations wrld)))
                 (wf-pending-p (mv-nth 1 (bx-event-items ev encl pending defined
                                                         translations wrld))
                               wrld)))
   :hints (("Goal"
            :use ((:instance wf-bx-program-defs
                             (names (bx-names (bx-ev-namex ev)))
                             (form (bx-ev-form ev))
                             (defs nil) (notes nil)))
            :in-theory
            (e/d (wf-event-data-p)
                 (bx-ev-type bx-ev-namex bx-ev-symbol-class bx-ev-form bx-names
                  bx-all-program-p bx-some-program-p bx-all-constrained-p
                  bx-some-constrained-p bx-constrained-p bx-constrainer
                  bx-define-items bx-program-defs bx-reserve-items bx-stobj-items
                  bx-constrain-items bx-package-items bx-choose-items
                  bx-add-candidates bx-definition-candidates bx-formula-name
                  wf-bx-program-defs wf-translations-p
                  wf-encapsulate-data-p wf-choice-second-formals-p
                  wf-function-name-list-p wf-ground-functions-p))))))

;;; Selecting events from the world, pairing them with their enclosing
;;; encapsulates, and transferring their items to the result.

(defun wf-events-p (evs wrld)
  (if (consp evs)
      (and (wf-event-data-p (car evs) wrld) (wf-events-p (cdr evs) wrld))
    (null evs)))

(defun wf-event-pairs-p (pairs wrld)
  (if (consp pairs)
      (and (wf-event-data-p (caar pairs) wrld) (wf-event-pairs-p (cdr pairs) wrld))
    (null pairs)))

(local
 (defthm wf-events-p-of-revappend
   (implies (and (wf-events-p a wrld) (wf-events-p b wrld))
            (wf-events-p (revappend a b) wrld))))

(local
 (defthm wf-events-p-of-reverse
   (implies (wf-events-p a wrld) (wf-events-p (reverse a) wrld))))

(local
 (defthm wf-bx-events
   (implies (and (wf-world-event-data-p tail wrld lo hi) (wf-events-p acc wrld))
            (wf-events-p (bx-events tail lo hi acc) wrld))
   :hints (("Goal" :induct (bx-events tail lo hi acc)
            :in-theory (disable bx-ev-number)))))

(local
 (defthm wf-bx-enclose
   (implies (and (wf-events-p evs wrld) (wf-event-pairs-p acc wrld))
            (wf-event-pairs-p (bx-enclose evs stack acc wrld) wrld))
   :hints (("Goal" :induct (bx-enclose evs stack acc wrld)
            :in-theory (disable bx-ev-type bx-ev-depth bx-constrainer
                                bx-first-constrainer bx-pop)))))

(local
 (defthm wf-bx-items
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-translations-p translations)
                 (wf-event-pairs-p pairs wrld)
                 (wf-pending-p pending wrld)
                 (wf-items-p acc))
            (wf-items-p (bx-items pairs pending defined translations wrld acc)))
   :hints (("Goal" :induct (bx-items pairs pending defined translations wrld acc)
            :in-theory (disable bx-event-items bx-add-defined bx-add-candidates
                                bx-select bx-items-used bx-items-introduced bx-later-items)))))

(defthm wf-bx-range-items
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-world-event-data-p wrld wrld lo hi)
                (wf-translations-p translations))
           (wf-items-p (bx-range-items lo hi translations wrld)))
  :hints (("Goal" :in-theory (disable bx-items bx-enclose bx-events))))

;;; A translated program body can change program items and notes. The
;;; selection of statements and the tables that drive later statements
;;; depend only on the statement items and the pending constraints.

(local
 (defthm wf-select-statements-of-append
   (equal (bx-select :stmt (append a b))
          (append (bx-select :stmt a) (bx-select :stmt b)))))

(local
 (defthm wf-select-statements-of-revappend
   (equal (bx-select :stmt (revappend a b))
          (revappend (bx-select :stmt a) (bx-select :stmt b)))))

(local
 (defthm wf-select-statements-of-reverse
   (equal (bx-select :stmt (reverse a))
          (reverse (bx-select :stmt a)))))

(local
 (defthm wf-no-statements-in-program-notes
   (implies (not (bx-select :stmt notes))
            (equal (bx-select :stmt
                              (mv-nth 1 (bx-program-defs names form translations
                                                        wrld defs notes)))
                   nil))
   :hints (("Goal" :induct (bx-program-defs names form translations wrld defs notes)
            :in-theory (disable bx-program-body)))))

(local
 (defthm wf-no-function-uses-without-statements
   (implies (not (bx-select :stmt items))
            (equal (bx-items-used items) nil))
   :hints (("Goal" :induct (bx-items-used items)))))

;;; Deferral requires a function used by a statement. Translation can
;;; affect the items of a program definition, which has no statement.

(local
 (defthm wf-event-results-for-statements
   (let* ((results (bx-event-items ev encl pending defined translations wrld))
          (other-results (bx-event-items ev encl pending defined nil wrld))
          (items (car results))
          (other-items (car other-results)))
     (and (equal (mv-nth 1 results) (mv-nth 1 other-results))
          (equal (bx-select :stmt items) (bx-select :stmt other-items))
          (equal (bx-items-used items) (bx-items-used other-items))
          (implies (bx-items-used items) (equal items other-items))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (disable bx-ev-type bx-ev-namex bx-ev-symbol-class bx-ev-form bx-names
                     bx-all-program-p bx-some-program-p bx-all-constrained-p
                     bx-some-constrained-p bx-constrained-p bx-constrainer
                     bx-program-defs bx-constrain-items bx-choose-items
                     bx-package-items bx-define-items bx-stobj-items bx-reserve-items
                     bx-items-used)))))

(local
 (defun wf-add-defined-from-statements (stmts defined)
   (if (consp stmts)
       (wf-add-defined-from-statements
        (cdr stmts)
        (if (member-equal (caar stmts) '("define" "constrain" "choose"))
            (bx-add-names (bx-introduced (car stmts)) defined)
          defined))
     defined)))

(local
 (defthm wf-bx-add-defined-uses-statements
   (equal (bx-add-defined items defined)
          (wf-add-defined-from-statements (bx-select :stmt items) defined))
   :hints (("Goal" :induct (bx-add-defined items defined)
            :in-theory (disable bx-introduced bx-add-names)))))

(local
 (defthm wf-intersection-needs-first-list
   (implies (intersectp-equal a b) a)
   :rule-classes :forward-chaining))

(local
 (defun wf-statements-induction (pairs pending defined translations wrld acc other)
   (if (atom pairs)
       (list acc other)
     (let ((ev (caar pairs)) (encl (cdar pairs)))
       (mv-let (items next-pending)
         (bx-event-items ev encl pending defined translations wrld)
         (mv-let (other-items other-pending)
           (bx-event-items ev encl pending defined nil wrld)
           (declare (ignore other-pending))
           (let ((defined (bx-add-defined items defined)))
             (if (and encl
                      (intersectp-eq
                       (bx-items-used items)
                       (append (getpropc encl 'siblings nil wrld)
                               (bx-items-introduced
                                (bx-later-items (cdr (assoc-eq encl next-pending)))))))
                 (wf-statements-induction
                  (cdr pairs)
                  (bx-add-candidates encl (list (list nil :after items)) next-pending)
                  defined translations wrld acc other)
               (wf-statements-induction (cdr pairs) next-pending defined translations wrld
                                        (revappend items acc)
                                        (revappend other-items other))))))))))

(local
 (defthm wf-accumulated-statements-ignore-translations
   (implies (equal (bx-select :stmt acc) (bx-select :stmt other))
            (equal (bx-select :stmt
                              (bx-items pairs pending defined translations wrld acc))
                   (bx-select :stmt
                              (bx-items pairs pending defined nil wrld other))))
   :rule-classes nil
   :hints (("Goal" :induct (wf-statements-induction pairs pending defined translations
                                                   wrld acc other)
            :in-theory (disable bx-add-defined bx-event-items bx-add-candidates
                                bx-items-used bx-items-introduced bx-later-items
                                intersectp-equal assoc-equal))
           ("Subgoal *1/3"
            :use ((:instance wf-event-results-for-statements
                             (ev (caar pairs)) (encl (cdar pairs)))))
           ("Subgoal *1/2"
            :use ((:instance wf-event-results-for-statements
                             (ev (caar pairs)) (encl (cdar pairs))))))))

(defthm wf-item-statements-ignore-translations
  (implies (syntaxp (not (equal translations ''nil)))
           (equal (bx-select :stmt (bx-items pairs pending defined translations wrld acc))
                  (bx-select :stmt (bx-items pairs pending defined nil wrld acc))))
  :hints (("Goal" :use ((:instance wf-accumulated-statements-ignore-translations
                                   (other acc)))
           :in-theory (disable bx-items))))

(defthm wf-range-statements-ignore-translations
  (implies (syntaxp (not (equal translations ''nil)))
           (equal (bx-select :stmt (bx-range-items lo hi translations wrld))
                  (bx-select :stmt (bx-range-items lo hi nil wrld))))
  :hints (("Goal" :in-theory (disable bx-events bx-enclose bx-items))))
