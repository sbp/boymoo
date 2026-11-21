(in-package "ACL2")

(include-book "structure-events")
(include-book "structure-walk")

; A coverage note names a missing or unsupported name in the position
; assigned to it by the note's kind.  A symbol occurring incidentally
; inside another name's diagnostic does not account for that symbol.

(defun structure-note-names (reason data)
  (cond
   ((member-equal reason
                  '("name of no known kind"
                    "stobj function with no definition"
                    "package that ACL2 does not know"
                    "defchoose axiom not of the form of spec/logic.md"
                    "constrained choice outside an encapsulate"
                    "constrained choice of a function that its constraint does not list"))
    (list data))
   ((member-equal reason '("logic event of a function now in program mode"
                           "clique only partly constrained"
                           "constrained definition outside an encapsulate"
                           "constrained definition of functions that its constraint does not list"
                           "constraint with a formula for which no unused name was found"))
    data)
   ((equal reason "event of an unexpected kind") (cadr data))
   ((equal reason "event of an encapsulate whose formula is not in its constraint")
    (list (cadr data)))
   (t nil)))

(defun structure-note-reports-p (name line)
  (and (equal (car line) "note")
       (member-equal name (structure-note-names (caadr line) (cadadr line)))))

(defun structure-notes-report-p (name notes)
  (and (consp notes)
       (or (structure-note-reports-p name (car notes))
           (structure-notes-report-p name (cdr notes)))))

(defun structure-event-line-supplies-p (name line)
  (and (or (stringp name) (not (structure-package-linep line)))
       (structure-line-supplies-p name line)))

(defun structure-event-lines-supply-p (name lines)
  (and (consp lines)
       (or (structure-event-line-supplies-p name (car lines))
           (structure-event-lines-supply-p name (cdr lines)))))

(defthm structure-event-supplies-implies-supplies
  (implies (structure-event-lines-supply-p name lines)
           (structure-lines-supply-p name lines))
  :hints (("Goal" :in-theory (disable structure-line-supplies-p))))

(defun structure-item-accounts-for-p (name item)
  (case (car item)
    (:stmt (structure-event-line-supplies-p name (cdr item)))
    (:note (member-equal name (structure-note-names (cadr item) (caddr item))))
    (otherwise nil)))

(defun structure-items-account-for-p (name items)
  (and (consp items)
       (or (structure-item-accounts-for-p name (car items))
           (structure-items-account-for-p name (cdr items)))))

(defthm structure-item-coverage-of-append
  (iff (structure-items-account-for-p name (append a b))
       (or (structure-items-account-for-p name a)
           (structure-items-account-for-p name b))))

(defthm structure-item-coverage-of-revappend
  (iff (structure-items-account-for-p name (revappend a b))
       (or (structure-items-account-for-p name a)
           (structure-items-account-for-p name b)))
  :hints (("Goal" :induct (revappend a b)
                  :in-theory (disable structure-item-accounts-for-p))))

(defthm structure-item-coverage-of-reverse
  (iff (structure-items-account-for-p name (reverse items))
       (structure-items-account-for-p name items))
  :hints (("Goal" :in-theory (disable revappend))))

(defthm structure-coverage-is-statement-or-note
  (iff (structure-items-account-for-p name items)
       (or (structure-event-lines-supply-p name (bx-select :stmt items))
           (structure-notes-report-p name (bx-note-lines (bx-select :note items)))))
  :hints (("Goal" :induct (structure-items-account-for-p name items)
                  :in-theory (disable structure-note-names structure-line-supplies-p))))

; The constructors for single events retain the names they take.  A
; single-threaded object's definitions can be rearranged, including when
; the local ordering attempt cannot finish.

(local (in-theory (disable structure-items-account-for-p
                           structure-item-coverage-of-append
                           structure-coverage-is-statement-or-note)))

(defthm structure-item-coverage-of-cons
  (iff (structure-items-account-for-p name (cons item rest))
       (or (structure-item-accounts-for-p name item)
           (structure-items-account-for-p name rest)))
  :hints (("Goal" :in-theory (enable structure-items-account-for-p))))

(defthm structure-item-coverage-of-nil
  (not (structure-items-account-for-p name nil))
  :hints (("Goal" :in-theory (enable structure-items-account-for-p))))

(local (in-theory (enable structure-item-coverage-of-append)))

(defthm structure-defs-keep-names
  (equal (strip-cars (bx-defs names wrld))
         (true-list-fix names)))

(defthm structure-member-of-true-list-fix
  (iff (member-equal name (true-list-fix names))
       (member-equal name names)))

(defthm structure-define-items-cover
  (implies (and (not (stringp name))
                (member-equal name names))
           (structure-items-account-for-p name (bx-define-items names wrld)))
  :hints (("Goal" :in-theory (disable bx-defs bx-rulers bx-same-rulers))))

(defthm structure-package-items-cover
  (implies (stringp name)
           (structure-items-account-for-p name (bx-package-items name form wrld)))
  :hints (("Goal" :in-theory (disable global-val))))

(defthm structure-choose-items-cover
  (implies (not (stringp name))
           (structure-items-account-for-p name (bx-choose-items name wrld)))
  :hints (("Goal" :in-theory (disable bx-choose-parts bx-choose-axiom bx-beta formals))))

(defthm structure-reserve-items-cover
  (implies (and (not (stringp name))
                (member-equal name names))
           (structure-items-account-for-p name (bx-reserve-items names wrld)))
  :hints (("Goal" :induct (bx-reserve-items names wrld)
                  :in-theory (disable bx-reserve-kind-p))))

(defthm structure-stobj-define-items-cover
  (implies (and (not (stringp name))
                (member-equal name names))
           (structure-items-account-for-p name (bx-stobj-define-items names wrld)))
  :hints (("Goal" :in-theory (disable bx-define-items))))

(defthm structure-member-of-set-difference
  (iff (member-equal name (set-difference-equal a b))
       (and (member-equal name a)
            (not (member-equal name b)))))

(defthm structure-local-order-keeps-name
  (implies (or (member-equal name todo) (member-equal name acc))
           (member-equal name (bx-local-order todo placed acc wrld fuel)))
  :hints (("Goal" :induct (bx-local-order todo placed acc wrld fuel)
                  :in-theory (disable bx-ready revappend reverse set-difference-equal))))

(defthm structure-stobj-items-cover
  (implies
   (and (not (stringp name))
        (or (member-equal name names)
            (member-equal name fns-acc)
            (structure-items-account-for-p name acc))
        (not (and (bx-function-p name wrld)
                  (or (hons-get name defined) (bx-programp name wrld)))))
   (structure-items-account-for-p name (bx-stobj-items names defined fns-acc wrld acc)))
  :hints (("Goal" :induct (bx-stobj-items names defined fns-acc wrld acc)
                  :in-theory (disable bx-function-p bx-programp bx-reserve-kind-p
                                      bx-stobj-define-items bx-local-order bx-exec
                                      revappend reverse hons-get))))

; A constraint can introduce both its signatures and any of its siblings.
; For a theorem moved to the constraint, its candidate supplies either a
; formula of that name or the note about its missing formula.

(defthm structure-member-of-insert-by-event
  (iff (member-equal name (bx-insert-by-event fn fns wrld))
       (or (equal name fn) (member-equal name fns)))
  :hints (("Goal" :in-theory (disable bx-event-number))))

(defthm structure-sort-by-event-keeps-name
  (iff (member-equal name (bx-sort-by-event fns wrld))
       (member-equal name fns))
  :hints (("Goal" :in-theory (disable bx-insert-by-event))))

(defthm structure-arities-keep-names
  (equal (strip-cars (bx-arities fns wrld))
         (true-list-fix fns))
  :hints (("Goal" :in-theory (disable formals))))

(defthm structure-member-of-strip-cars-of-append
  (iff (member-equal name (strip-cars (append a b)))
       (or (member-equal name (strip-cars a))
           (member-equal name (strip-cars b)))))

(defthm structure-member-of-strip-cars-of-revappend
  (iff (member-equal name (strip-cars (revappend a b)))
       (or (member-equal name (strip-cars a))
           (member-equal name (strip-cars b))))
  :hints (("Goal" :induct (revappend a b))))

(defthm structure-member-of-strip-cars-of-reverse
  (iff (member-equal name (strip-cars (reverse a)))
       (member-equal name (strip-cars a)))
  :hints (("Goal" :in-theory (disable revappend))))

(defthm structure-candidate-formulas-keep-names
  (equal (strip-cars (bx-candidate-formulas candidates wrld))
         (strip-cars candidates))
  :hints (("Goal" :in-theory (disable formals))))

(local (in-theory (disable bx-candidate-formulas bx-arities bx-sort-by-event
                           bx-conjuncts bx-equation-in bx-remove-guard-holders
                           revappend reverse)))

(defthm structure-candidate-terms-account-for-name
  (implies
   (or (member-equal name (strip-cars candidates))
       (member-equal name (strip-cars formulas))
       (structure-items-account-for-p name notes))
   (let ((result (bx-candidate-terms candidates constraints root wrld formulas covered notes)))
     (or (member-equal name (strip-cars (car result)))
         (structure-items-account-for-p name (mv-nth 2 result)))))
  :hints (("Goal" :induct (bx-candidate-terms candidates constraints root wrld
                                              formulas covered notes)
                  :in-theory (disable union-equal))))

(defthm structure-name-formulas-account-for-name
  (implies (member-equal name (strip-cars candidates))
           (let ((result (bx-name-formulas constraints candidates root wrld)))
             (or (member-equal name (strip-cars (car result)))
                 (structure-items-account-for-p name (mv-nth 1 result)))))
  :hints (("Goal" :use ((:instance structure-candidate-terms-account-for-name
                                   (formulas nil) (covered nil) (notes nil)))
                  :in-theory (disable bx-candidate-terms bx-uncovered
                                      structure-candidate-terms-account-for-name))))

; An exhaustion note accounts for the constraint's functions and every
; formula that has a name.

(defthm structure-nonnil-name-survives-removal
  (implies (and name (member-equal name names))
           (member-equal name (remove-equal nil names))))

(defthm structure-constrain-statement-accounts-for-function
  (implies (and (not (stringp name)) (member-equal name fns))
           (structure-items-account-for-p name (bx-constrain-stmt fns formulas wrld))))

(defthm structure-constrain-statement-accounts-for-formula
  (implies (and name
                (not (stringp name))
                (member-equal name (strip-cars formulas)))
           (structure-items-account-for-p name (bx-constrain-stmt fns formulas wrld)))
  :hints (("Goal" :in-theory (disable remove-equal))))

(defthm structure-constrain-items-account-for-function
  (implies (and (not (stringp name))
                (or (member-equal name names)
                    (member-equal name (getpropc root 'siblings nil wrld))))
           (structure-items-account-for-p name (bx-constrain-items names root pending wrld)))
  :hints (("Goal" :in-theory (disable bx-constrain-stmt bx-name-formulas constraint-info
                                      bx-formula-cands bx-later-items set-difference-equal))))

(defthm structure-constrain-items-account-for-formula
  (let ((candidates (bx-formula-cands (cdr (assoc-eq root pending)))))
    (implies (and name
                  (not (stringp name))
                  (member-equal name (strip-cars candidates)))
             (structure-items-account-for-p name (bx-constrain-items names root pending wrld))))
  :hints (("Goal"
           :use ((:instance structure-name-formulas-account-for-name
                            (candidates (bx-formula-cands (cdr (assoc-eq root pending))))
                            (constraints (mv-nth 1 (constraint-info root wrld)))))
           :in-theory (disable bx-constrain-stmt bx-name-formulas constraint-info
                               bx-formula-cands bx-later-items set-difference-equal
                               structure-name-formulas-account-for-name))))
