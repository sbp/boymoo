(in-package "ACL2")

(include-book "guards-terms")

(local
 (in-theory (disable fgetprop formals plist-worldp bx-world-properties-p
                     bx-ev-unlocal bx-ev-type bx-ev-namex bx-ev-symbol-class
                     bx-event-tuple-p bx-event-fields-p bx-ev-form
                     bx-ev-depth bx-ev-number bx-names bx-defun-form-p
                     bx-choice-input-p bx-constraint-owner-p constraint-info
                     bx-constrained-p bx-programp bx-function-p
                     pseudo-termp pseudo-term-listp hons-get all-fnnames1)))

; Event ranges preserve the facts needed when reading each event.

(defthm bx-true-listp-of-event-list
  (implies (bx-event-list-p evs) (true-listp evs))
  :rule-classes (:forward-chaining :rewrite))

(defthm bx-true-listp-of-event-names
  (implies (bx-event-names-p ev)
           (true-listp (bx-names (bx-ev-namex ev)))))

(verify-guards bx-event-data-p)
(verify-guards bx-event-data-list-p
  :hints (("Goal" :in-theory (disable bx-event-data-p bx-event-names-p))))
(verify-guards bx-event-data-world-p
  :hints (("Goal" :in-theory (disable bx-event-data-p bx-event-names-p))))
(verify-guards bx-export-world-p)
(verify-guards bx-enclosed-events-p
  :hints (("Goal" :in-theory (disable bx-event-data-p bx-event-names-p))))

(local
 (defthm bx-event-data-entails-constraint
   (implies (bx-event-data-p ev wrld) (bx-event-constraint-p ev wrld))))

(local
 (in-theory (disable bx-event-names-p bx-event-data-p bx-event-constraint-p)))

(local
 (defthm bx-event-constraints-from-event-data-list
   (implies (bx-event-data-list-p evs wrld)
            (bx-event-constraints-p evs wrld))))

(local
 (defthm bx-events-preserve-event-data
   (implies (and (bx-event-data-world-p tail wrld)
                 (bx-event-data-list-p acc wrld))
            (bx-event-data-list-p (bx-events tail lo hi acc) wrld))
   :hints (("Goal" :induct (bx-events tail lo hi acc)))))

(local
 (defthm bx-event-data-list-p-of-revappend
   (implies (and (bx-event-data-list-p x wrld) (bx-event-data-list-p y wrld))
            (bx-event-data-list-p (revappend x y) wrld))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defthm bx-event-list-p-of-revappend
   (implies (and (bx-event-list-p x) (bx-event-list-p y))
            (bx-event-list-p (revappend x y)))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defun bx-stack-owners-p (stack wrld)
   (declare (xargs :verify-guards nil))
   (if (consp stack)
       (and (symbolp (cdar stack))
            (or (not (cdar stack)) (bx-constraint-owner-p (cdar stack) wrld))
            (bx-stack-owners-p (cdr stack) wrld))
     (null stack))))

(local
 (defthm bx-stack-owners-of-pop
   (implies (bx-stack-owners-p stack wrld)
            (bx-stack-owners-p (bx-pop stack d) wrld))))

(local
 (defthm bx-owner-of-first-constrainer
   (implies (and (bx-stack-owners-p stack wrld) (bx-first-constrainer stack))
            (bx-constraint-owner-p (bx-first-constrainer stack) wrld))))

(local
 (defthm bx-symbolp-of-first-constrainer
   (implies (bx-depth-stack-p stack)
            (symbolp (bx-first-constrainer stack)))))

(local
 (defthm bx-constrainer-without-signature
   (implies (or (not (equal (bx-ev-type ev) 'encapsulate))
                (not (consp (bx-ev-namex ev))))
            (equal (bx-constrainer ev wrld) nil))
   :hints (("Goal" :in-theory (disable constraint-info)))))

(local
 (defthm bx-stack-context-of-constrainer
   (implies (and (bx-event-names-p ev) (bx-event-constraint-p ev wrld))
            (symbolp (bx-constrainer ev wrld)))
   :hints (("Goal" :cases ((and (equal (bx-ev-type ev) 'encapsulate)
                                (consp (bx-ev-namex ev))))
            :in-theory (disable bx-constrainer)))))

(local
 (defthm bx-owner-of-nonempty-constrainer
   (implies (and (bx-event-names-p ev) (bx-event-constraint-p ev wrld)
                 (bx-constrainer ev wrld))
            (bx-constraint-owner-p (bx-constrainer ev wrld) wrld))
   :hints (("Goal" :cases ((and (equal (bx-ev-type ev) 'encapsulate)
                                (consp (bx-ev-namex ev))))
            :in-theory (disable bx-constrainer)))))

(local
 (defthm bx-enclosed-events-of-enclose
   (implies (and (bx-event-list-p evs)
                 (bx-event-data-list-p evs wrld)
                 (bx-depth-stack-p stack)
                 (bx-stack-owners-p stack wrld)
                 (bx-enclosed-events-p acc wrld))
            (bx-enclosed-events-p (bx-enclose evs stack acc wrld) wrld))
   :hints (("Goal" :induct (bx-enclose evs stack acc wrld)
            :in-theory (disable bx-pop bx-first-constrainer bx-constrainer)))))

(defthm bx-enclosed-event-range
  (implies (bx-export-world-p wrld)
           (bx-enclosed-events-p
            (bx-enclose (reverse (bx-events wrld lo hi nil)) nil nil wrld)
            wrld))
  :hints (("Goal" :in-theory (disable bx-enclose bx-events))))

; The selectors use the line-specific lists of names and terms.

(verify-guards bx-definitions-p)
(verify-guards bx-named-formulas-p)
(verify-guards bx-arity-list-p)
(verify-guards bx-line-p)
(verify-guards bx-line-list-p)
(verify-guards bx-definition-lines-p)
(verify-guards bx-item-list-p)
(verify-guards bx-bodies)

(defthm bx-line-p-implies-cons
  (implies (bx-line-p x)
           (and (consp x) (true-listp x)))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-definition-list-structure
  (implies (bx-definitions-p defs)
           (and (alistp defs)
                (true-list-listp defs)
                (pseudo-term-listp (bx-bodies defs))
                (symbol-listp (strip-cars defs))))
  :hints (("Goal" :induct (bx-definitions-p defs)
           :in-theory (enable pseudo-term-listp))))

(defthm bx-named-formula-list-structure
  (implies (bx-named-formulas-p formulas)
           (and (alistp formulas)
                (all->=-len formulas 2)
                (symbol-listp (strip-cars formulas))
                (pseudo-term-listp (strip-cadrs formulas))))
  :hints (("Goal" :induct (bx-named-formulas-p formulas)
           :in-theory (enable pseudo-term-listp all->=-len))))

(defthm bx-arities-list-structure
  (implies (bx-arity-list-p pairs)
           (and (alistp pairs)
                (true-list-listp pairs)
                (all->=-len pairs 2)
                (symbol-listp (strip-cars pairs))))
  :hints (("Goal" :induct (bx-arity-list-p pairs)
           :in-theory (enable all->=-len))))

(verify-guards bx-introduced
  :hints (("Goal" :in-theory (disable bx-definitions-p bx-arity-list-p))))
(verify-guards bx-used
  :hints (("Goal" :in-theory (disable bx-definitions-p bx-arity-list-p
                                     bx-named-formulas-p bx-bodies))))

(defthm bx-symbol-listp-of-introduced
  (implies (bx-line-p stmt) (symbol-listp (bx-introduced stmt)))
  :hints (("Goal" :in-theory (disable bx-definitions-p bx-arity-list-p strip-cars))))

(local
 (defthm bx-symbol-listp-of-set-difference
   (implies (symbol-listp x) (symbol-listp (set-difference-equal x y)))))

(defthm bx-symbol-listp-of-used
  (implies (bx-line-p stmt) (symbol-listp (bx-used stmt)))
  :hints (("Goal" :in-theory (disable bx-definitions-p bx-arity-list-p
                                     bx-named-formulas-p bx-bodies strip-cars
                                     strip-cadrs set-difference-equal))))

(defthm bx-line-listp-implies-alistp
  (implies (bx-line-list-p x) (alistp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-definition-lines-imply-lines
  (implies (bx-definition-lines-p x) (bx-line-list-p x))
  :hints (("Goal" :in-theory (disable bx-line-p)))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-item-listp-implies-alistp
  (implies (bx-item-list-p x) (alistp x))
  :hints (("Goal" :in-theory (disable bx-line-p)))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-item-listp-implies-true-listp
  (implies (bx-item-list-p x) (true-listp x))
  :hints (("Goal" :in-theory (disable bx-item-list-p)))
  :rule-classes :forward-chaining)

(defthm bx-item-listp-of-append
  (implies (and (bx-item-list-p x) (bx-item-list-p y))
           (bx-item-list-p (append x y)))
  :hints (("Goal" :in-theory (disable bx-line-p))))

(defthm bx-item-list-p-of-cons-note
  (equal (bx-item-list-p (cons (bx-note key data) items))
         (bx-item-list-p items)))

(local
 (defthm bx-item-listp-of-revappend
   (implies (and (bx-item-list-p x) (bx-item-list-p y))
            (bx-item-list-p (revappend x y)))
   :hints (("Goal" :induct (revappend x y)))))

(verify-guards bx-select)
(verify-guards bx-add-names)
(verify-guards bx-add-defined
  :hints (("Goal" :in-theory (disable bx-line-p bx-introduced))))
(verify-guards bx-items-used
  :hints (("Goal" :in-theory (disable bx-line-p bx-used))))
(verify-guards bx-items-introduced
  :hints (("Goal" :in-theory (disable bx-line-p bx-introduced))))

(defthm bx-select-statements-are-lines
  (implies (bx-item-list-p items)
           (bx-line-list-p (bx-select :stmt items)))
  :hints (("Goal" :induct (bx-select :stmt items) :in-theory (disable bx-line-p))))

(defthm bx-select-programs-are-definition-lines
  (implies (bx-item-list-p items)
           (bx-definition-lines-p (bx-select :prog items)))
  :hints (("Goal" :induct (bx-select :prog items) :in-theory (disable bx-line-p))))

(defthm bx-select-notes-are-lists
  (implies (bx-item-list-p items)
           (true-list-listp (bx-select :note items)))
  :hints (("Goal" :induct (bx-select :note items) :in-theory (disable bx-line-p))))

(local
 (defthm bx-symbol-listp-of-items-introduced
   (implies (bx-item-list-p items)
            (symbol-listp (bx-items-introduced items)))
   :hints (("Goal" :in-theory (disable bx-line-p bx-introduced)))))

(local
 (defthm bx-symbol-listp-of-items-used
   (implies (bx-item-list-p items) (symbol-listp (bx-items-used items)))
   :hints (("Goal" :in-theory (disable bx-line-p bx-used)))))

; Lists of definitions are constructed from stored bodies or translated
; program bodies. The stobj ordering only permutes the functions supplied.

(verify-guards bx-translations-p)

(local
 (defthm bx-translation-alist-p
   (implies (bx-translations-p xs) (alistp xs))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm bx-translation-value-from-assoc
   (implies (bx-translations-p xs)
            (and (listp (cdr (assoc-equal fn xs)))
                 (implies (eq (cadr (assoc-equal fn xs)) :ok)
                          (pseudo-termp (cddr (assoc-equal fn xs))))))
   :hints (("Goal" :induct (assoc-equal fn xs)))))

(verify-guards bx-program-body
  :hints (("Goal" :in-theory (disable bx-defun-forms bx-definition-forms-p
                                     bx-needs-translation-p))))

(local
 (defthm bx-program-body-is-pseudo-term
   (implies (and (bx-world-properties-p wrld) (bx-translations-p translations))
            (pseudo-termp (car (bx-program-body fn form translations wrld))))
   :hints (("Goal" :in-theory (disable bx-defun-forms member-equal)))))

(local
 (defthm bx-program-body-note-shape
   (let ((note (mv-nth 1 (bx-program-body fn form translations wrld))))
     (implies note
              (and (consp note) (eq (car note) :note) (true-listp (cdr note)))))
   :hints (("Goal" :in-theory (disable bx-defun-forms member-equal)))))

(local
 (defthm bx-true-listp-of-definitions
   (implies (bx-definitions-p defs) (true-listp defs))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm bx-definitions-p-of-revappend
   (implies (and (bx-definitions-p defs) (bx-definitions-p acc))
            (bx-definitions-p (revappend defs acc)))
   :hints (("Goal" :induct (revappend defs acc)))))

(verify-guards bx-program-defs
  :hints (("Goal" :in-theory (disable bx-program-body bx-exec bx-defun-forms))))

(local
 (defthm bx-program-defs-shape
   (implies (and (symbol-listp fns)
                 (bx-world-properties-p wrld) (bx-translations-p translations)
                 (bx-definitions-p defs) (bx-item-list-p notes))
            (and (bx-definitions-p
                  (car (bx-program-defs fns form translations wrld defs notes)))
                 (bx-item-list-p
                  (mv-nth 1 (bx-program-defs fns form translations wrld defs notes)))))
   :hints (("Goal" :induct (bx-program-defs fns form translations wrld defs notes)
            :in-theory (disable bx-program-body bx-exec)))))

(local
 (defthm bx-program-defs-notes-are-list
   (implies (true-listp notes)
            (true-listp (mv-nth 1 (bx-program-defs fns form translations wrld defs notes))))
   :hints (("Goal" :induct (bx-program-defs fns form translations wrld defs notes)
            :in-theory (disable bx-program-body bx-exec)))))

(local
 (defthm bx-logical-definitions-shape
   (implies (and (symbol-listp fns) (bx-world-properties-p wrld))
            (bx-definitions-p (bx-defs fns wrld)))))

(verify-guards bx-define-items)
(verify-guards bx-ready
  :hints (("Goal" :in-theory (disable set-difference-equal intersection-equal))))

(local
 (defthm bx-ready-preserves-functions
   (implies (symbol-listp todo)
            (and (symbol-listp (bx-ready todo placed wrld))
                 (implies (bx-functions-present-p todo wrld)
                          (bx-functions-present-p (bx-ready todo placed wrld) wrld))))
   :hints (("Goal" :induct (bx-ready todo placed wrld)
            :in-theory (disable set-difference-equal intersection-equal)))))

(defthm bx-present-functions-of-append
  (implies (and (bx-functions-present-p x wrld) (bx-functions-present-p y wrld))
           (bx-functions-present-p (append x y) wrld)))

(local
 (defthm bx-present-functions-of-revappend
   (implies (and (bx-functions-present-p x wrld) (bx-functions-present-p y wrld))
            (bx-functions-present-p (revappend x y) wrld))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defthm bx-present-functions-of-set-difference
   (implies (bx-functions-present-p x wrld)
            (bx-functions-present-p (set-difference-equal x y) wrld))))

(local
 (defthm bx-symbol-listp-of-revappend
   (implies (and (symbol-listp x) (symbol-listp y))
            (symbol-listp (revappend x y)))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defthm bx-symbol-listp-of-append
   (implies (and (symbol-listp x) (symbol-listp y))
            (symbol-listp (append x y)))))

(verify-guards bx-local-order
  :hints (("Goal" :in-theory (disable bx-ready))))

(local
 (defthm bx-local-order-preserves-functions
   (implies (and (symbol-listp todo) (symbol-listp acc)
                 (bx-functions-present-p todo wrld)
                 (bx-functions-present-p acc wrld))
            (and (symbol-listp (bx-local-order todo placed acc wrld fuel))
                 (bx-functions-present-p (bx-local-order todo placed acc wrld fuel)
                                          wrld)))
   :hints (("Goal" :induct (bx-local-order todo placed acc wrld fuel)
            :in-theory (disable bx-ready)))))

(verify-guards bx-stobj-define-items
  :hints (("Goal" :in-theory (disable bx-define-items))))
(verify-guards bx-stobj-items
  :hints (("Goal" :in-theory (disable bx-stobj-define-items bx-local-order bx-exec))))

(local
 (defthm bx-define-items-shape
   (implies (and (symbol-listp fns) (bx-world-properties-p wrld))
            (bx-item-list-p (bx-define-items fns wrld)))
   :hints (("Goal" :in-theory (disable bx-defs bx-rulers bx-same-rulers)))))

(local
 (defthm bx-stobj-define-items-shape
   (implies (and (symbol-listp fns) (bx-world-properties-p wrld))
            (bx-item-list-p (bx-stobj-define-items fns wrld)))
   :hints (("Goal" :in-theory (disable bx-define-items bx-item-list-p)))))

(local
 (defthm bx-stobj-items-shape
   (implies (and (symbol-listp names) (symbol-listp fns-acc)
                 (bx-functions-present-p fns-acc wrld)
                 (bx-world-properties-p wrld) (bx-item-list-p acc))
            (bx-item-list-p (bx-stobj-items names defined fns-acc wrld acc)))
   :hints (("Goal" :induct (bx-stobj-items names defined fns-acc wrld acc)
            :in-theory (disable bx-stobj-define-items bx-local-order bx-exec)))))

; The pending table separates formulas from items held until a constraint.

(verify-guards bx-candidate-list-p)
(verify-guards bx-pending-p)

(local
 (defthm bx-candidate-list-p-of-append
   (implies (and (bx-candidate-list-p x wrld flag) (bx-candidate-list-p y wrld flag))
            (bx-candidate-list-p (append x y) wrld flag))
   :hints (("Goal" :in-theory (disable bx-item-list-p)))))

(local
 (defthm bx-candidate-list-structure
   (implies (bx-candidate-list-p x wrld flag)
            (and (true-listp x) (all->=-len x 2) (bx-later-item-lists-p x)))
   :hints (("Goal" :in-theory (disable bx-item-list-p)))))

(local
 (defthm bx-pending-is-alist
   (implies (bx-pending-p pending wrld) (alistp pending))
   :hints (("Goal" :in-theory (disable bx-candidate-list-p)))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm bx-candidates-of-pending
   (implies (bx-pending-p pending wrld)
            (bx-candidate-list-p (cdr (assoc-equal c pending)) wrld t))
   :hints (("Goal" :induct (assoc-equal c pending)))))

(local
 (defthm bx-lists-of-pending
   (implies (bx-pending-p pending wrld)
            (and (true-listp (cdr (assoc-equal c pending)))
                 (all->=-len (cdr (assoc-equal c pending)) 2)
                 (bx-later-item-lists-p (cdr (assoc-equal c pending)))))
   :hints (("Goal" :use ((:instance bx-candidate-list-structure
                                   (x (cdr (assoc-equal c pending))) (flag t)))
            :in-theory (disable bx-candidate-list-structure)))))

(verify-guards bx-add-candidates)
(verify-guards bx-definition-candidates)
(verify-guards bx-formula-cands)
(verify-guards bx-later-item-lists-p)
(verify-guards bx-later-items
  :hints (("Goal" :in-theory (disable bx-item-list-p bx-line-p))))

(local
 (defthm bx-pending-p-of-put-assoc-equal
   (implies (and (bx-pending-p pending wrld)
                 (bx-candidate-list-p cands wrld t))
            (bx-pending-p (put-assoc-equal c cands pending) wrld))
   :hints (("Goal" :induct (put-assoc-equal c cands pending)
            :in-theory (disable bx-candidate-list-p)))))

(local
 (defthm bx-pending-p-of-add-candidates
   (implies (and (bx-pending-p pending wrld)
                 (bx-candidate-list-p cands wrld t))
            (bx-pending-p (bx-add-candidates c cands pending) wrld))
   :hints (("Goal" :in-theory (disable put-assoc-equal assoc-equal)))))

(local
 (defthm bx-formula-cands-of-candidate-list
   (implies (bx-candidate-list-p cands wrld t)
            (bx-candidate-list-p (bx-formula-cands cands) wrld nil))
   :hints (("Goal" :induct (bx-formula-cands cands)))))

(local
 (defthm bx-later-items-shape
   (implies (bx-later-item-lists-p cands)
            (bx-item-list-p (bx-later-items cands)))
   :hints (("Goal" :induct (bx-later-items cands)
            :in-theory (disable bx-item-list-p)))))

; A recognized equation is a member of the constraint's list of terms.

(local
 (defthm bx-candidates-are-true-list
   (implies (bx-candidate-list-p cands wrld flag) (true-listp cands))
   :hints (("Goal" :in-theory (disable bx-item-list-p)))
   :rule-classes :forward-chaining))

(local
 (defthm bx-named-formulas-are-true-list
   (implies (bx-named-formulas-p formulas) (true-listp formulas))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm bx-named-formulas-of-cons
   (equal (bx-named-formulas-p (cons (list name term) formulas))
          (and (symbolp name) (pseudo-termp term) (bx-named-formulas-p formulas)))))

(local
 (defthm bx-true-listp-of-union-equal
   (implies (true-listp y)
            (true-listp (union-equal x y)))))

(verify-guards bx-equation-in)

(local
 (defthm bx-pseudo-termp-of-equation-in
   (implies (pseudo-term-listp terms)
            (pseudo-termp (bx-equation-in fn terms wrld)))
   :hints (("Goal" :induct (bx-equation-in fn terms wrld)
            :in-theory (enable pseudo-term-listp)))))

(verify-guards bx-candidate-terms
  :hints (("Goal" :in-theory (disable bx-equation-in bx-conjuncts bx-note
                                     bx-item-list-p bx-named-formulas-p
                                     union-equal reverse)
           :do-not-induct t)))
(local
 (defthm bx-symbolp-of-fresh-name
   (symbolp (bx-fresh-name base i fn wrld fuel))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (disable bx-in-use-p explode-nonnegative-integer)))))

(local
 (defthm bx-symbolp-of-formula-name
   (symbolp (bx-formula-name fn word wrld))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (disable bx-fresh-name)))))

(verify-guards bx-uncovered
  :hints (("Goal" :in-theory (disable bx-formula-name explode-nonnegative-integer
                                     bx-note bx-item-list-p bx-named-formulas-p)
           :do-not-induct t)))

(local
 (defthm bx-named-formulas-of-append
   (implies (and (bx-named-formulas-p x) (bx-named-formulas-p y))
            (bx-named-formulas-p (append x y)))))

(local
 (defthm bx-named-formulas-of-revappend
   (implies (and (bx-named-formulas-p x) (bx-named-formulas-p y))
            (bx-named-formulas-p (revappend x y)))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defthm bx-candidate-terms-shape
   (implies (and (bx-candidate-list-p cands wrld nil) (pseudo-term-listp lst)
                 (bx-named-formulas-p formulas) (bx-item-list-p notes))
            (and (bx-named-formulas-p
                  (car (bx-candidate-terms cands lst c wrld formulas covered notes)))
                 (bx-item-list-p
                  (mv-nth 2 (bx-candidate-terms cands lst c wrld formulas covered notes)))))
   :hints (("Goal" :induct (bx-candidate-terms cands lst c wrld formulas covered notes)
            :in-theory (disable bx-equation-in bx-conjuncts bx-named-formulas-p
                                bx-item-list-p bx-note)))))

(local
 (defthm bx-uncovered-shape
   (implies (and (pseudo-term-listp lst)
                 (bx-named-formulas-p formulas) (bx-item-list-p notes))
            (and (bx-named-formulas-p (car (bx-uncovered lst covered c i wrld formulas notes)))
                 (bx-item-list-p (mv-nth 1 (bx-uncovered lst covered c i wrld formulas notes)))))
   :hints (("Goal" :induct (bx-uncovered lst covered c i wrld formulas notes)
            :in-theory (disable bx-formula-name explode-nonnegative-integer
                                bx-named-formulas-p bx-item-list-p bx-note)))))

(local
 (defthm bx-coverage-is-true-list
   (implies (true-listp covered)
            (true-listp (mv-nth 1 (bx-candidate-terms cands lst c wrld formulas covered notes))))
   :hints (("Goal" :induct (bx-candidate-terms cands lst c wrld formulas covered notes)
            :in-theory (disable bx-equation-in bx-conjuncts union-equal
                                bx-candidate-terms-shape bx-note bx-item-list-p
                                bx-named-formulas-p true-listp)))))

(verify-guards bx-name-formulas
  :hints (("Goal"
           :use ((:instance bx-item-listp-implies-true-listp
                            (x (mv-nth 2 (bx-candidate-terms cands lst c wrld nil nil nil)))))
           :in-theory (disable bx-candidate-terms bx-uncovered
                               bx-item-listp-implies-true-listp)
           :do-not-induct t)))

(local
 (defthm bx-name-formulas-shape
   (implies (and (pseudo-term-listp lst) (bx-candidate-list-p cands wrld nil))
            (and (bx-named-formulas-p (car (bx-name-formulas lst cands c wrld)))
                 (bx-item-list-p (mv-nth 1 (bx-name-formulas lst cands c wrld)))))
   :hints (("Goal" :in-theory (disable bx-candidate-terms bx-uncovered)))))

(local
 (defthm bx-true-listp-of-naming-notes
   (implies (and (pseudo-term-listp lst) (bx-candidate-list-p cands wrld nil))
            (true-listp (mv-nth 1 (bx-name-formulas lst cands c wrld))))
   :hints (("Goal"
            :use ((:instance bx-item-listp-implies-true-listp
                             (x (mv-nth 1 (bx-name-formulas lst cands c wrld)))))
            :in-theory (disable bx-name-formulas)))))

(verify-guards bx-insert-by-event
  :hints (("Goal" :in-theory (disable fgetprop))))

(local
 (defthm bx-insert-by-event-preserves-functions
   (implies (and (symbolp fn) (symbol-listp fns))
            (and (symbol-listp (bx-insert-by-event fn fns wrld))
                 (implies (and (bx-function-p fn wrld)
                               (bx-functions-present-p fns wrld))
                          (bx-functions-present-p (bx-insert-by-event fn fns wrld)
                                                  wrld))))
   :hints (("Goal" :induct (bx-insert-by-event fn fns wrld)
            :in-theory (disable bx-event-number)))))

(verify-guards bx-sort-by-event
  :hints (("Goal" :in-theory (disable bx-insert-by-event))))

(local
 (defthm bx-sort-by-event-preserves-functions
   (implies (symbol-listp fns)
            (and (symbol-listp (bx-sort-by-event fns wrld))
                 (implies (bx-functions-present-p fns wrld)
                          (bx-functions-present-p (bx-sort-by-event fns wrld) wrld))))
   :hints (("Goal" :induct (bx-sort-by-event fns wrld)
            :in-theory (disable bx-insert-by-event)))))

(verify-guards bx-candidate-formulas)
(verify-guards bx-constrain-stmt)

(local
 (defthm bx-constraint-owner-siblings
   (implies (bx-constraint-owner-p c wrld)
            (bx-functions-present-p (getpropc c 'siblings nil wrld) wrld))
   :hints (("Goal" :in-theory (enable bx-constraint-owner-p)))))

(local
 (defthm bx-constraint-owner-terms
   (let ((data (car (getpropc c 'constraint-lst-etc nil wrld))))
     (implies (and (bx-constraint-owner-p c wrld)
                   (not (unknown-constraints-p data)))
              (pseudo-term-listp data)))
   :hints (("Goal" :in-theory (enable bx-constraint-owner-p)))))

(local
 (defthm bx-constraint-owner-term-list
   (let ((data (car (getpropc c 'constraint-lst-etc nil wrld))))
     (implies (and (bx-constraint-owner-p c wrld)
                   (not (unknown-constraints-p data)))
              (true-listp data)))
   :hints (("Goal" :use bx-constraint-owner-terms
            :in-theory (disable bx-constraint-owner-terms unknown-constraints-p)))))

(local
 (defthm bx-candidate-formulas-shape
   (implies (and (bx-candidate-list-p cands wrld nil)
                 (bx-world-properties-p wrld))
            (bx-named-formulas-p (bx-candidate-formulas cands wrld)))
   :hints (("Goal" :in-theory (enable pseudo-term-listp)))))

(verify-guards bx-constrain-items
  :hints (("Goal" :in-theory (disable bx-later-items bx-candidate-formulas
                                     bx-sort-by-event bx-formula-cands
                                     bx-name-formulas bx-constrain-stmt)
           :do-not-induct t)))

(defthm bx-arities-shape
  (implies (symbol-listp fns)
           (bx-arity-list-p (bx-arities fns wrld))))

(local
 (defthm bx-no-quote-function-in-world
   (implies (bx-world-properties-p wrld)
            (not (bx-function-p 'quote wrld)))
   :hints (("Goal" :in-theory (enable bx-function-p)))))

(local
 (defthm bx-definition-candidates-shape
   (implies (and (symbol-listp fns)
                 (bx-functions-present-p fns wrld)
                 (bx-world-properties-p wrld))
            (bx-candidate-list-p (bx-definition-candidates fns wrld) wrld flag))
   :hints (("Goal" :induct (bx-definition-candidates fns wrld)
            :in-theory (disable bx-formula-name bx-item-list-p)))))

(local
 (defthm bx-constrain-stmt-shape
   (implies (and (symbol-listp fns) (bx-named-formulas-p formulas))
            (bx-item-list-p (bx-constrain-stmt fns formulas wrld)))
   :hints (("Goal" :in-theory (disable bx-arities bx-arity-list-p)))))

(local
 (defthm bx-constrain-items-shape
   (implies (and (symbol-listp names) (bx-constraint-owner-p c wrld)
                 (bx-world-properties-p wrld) (bx-pending-p pending wrld))
            (bx-item-list-p (bx-constrain-items names c pending wrld)))
   :hints (("Goal" :in-theory (disable bx-candidate-formulas bx-later-items
                                      bx-sort-by-event bx-name-formulas
                                      bx-constrain-stmt bx-formula-cands)))))

; The package table supplies imports even when there is no entry.

(defthm bx-known-package-alist-is-alist
  (implies (known-package-alistp known) (alistp known)))

(defthm bx-present-association-is-cons
  (implies (and (alistp xs) (assoc-equal key xs))
           (consp (assoc-equal key xs)))
  :hints (("Goal" :use bx-listp-of-assoc-equal
           :in-theory (disable assoc-equal))))

(defthm bx-package-entry-shape
  (implies (known-package-alistp known)
           (and (true-listp (find-package-entry name known))
                (symbol-listp (package-entry-imports (find-package-entry name known))))))

(defthm bx-package-entry-cons-fields
  (implies (known-package-alistp known)
           (and (iff (consp (cdr (find-package-entry name known)))
                     (cdr (find-package-entry name known)))
                (iff (consp (cddr (find-package-entry name known)))
                     (cddr (find-package-entry name known)))))
  :hints (("Goal" :use bx-package-entry-shape :in-theory (disable assoc-equal))))

(local
 (defthm bx-known-package-global-with-present-default
   (implies (known-package-alistp
             (getpropc 'known-package-alist 'global-value :missing wrld))
            (known-package-alistp (global-val 'known-package-alist wrld)))
   :hints (("Goal" :use ((:instance bx-fgetprop-change-default
                                    (name 'known-package-alist) (key 'global-value)
                                    (default :missing)
                                    (other (global-val 'known-package-alist nil))))
            :in-theory (disable known-package-alistp))
           ("Goal'" :in-theory (enable global-val)))))

(verify-guards bx-package-items
  :hints (("Goal" :in-theory (disable global-val assoc-equal
                                     known-package-alistp fgetprop)
           :do-not-induct t)))

(local
 (defthm bx-package-items-shape
   (implies (and (stringp name)
                 (bx-world-properties-p wrld)
                 (known-package-alistp
                  (getpropc 'known-package-alist 'global-value :missing wrld)))
            (bx-item-list-p (bx-package-items name form wrld)))
   :hints (("Goal" :in-theory (disable global-val assoc-equal known-package-alistp
                                bx-world-theorem bx-package-import-formula-p))
           (and stable-under-simplificationp
                '(:use ((:instance bx-world-theorem
                                   (name (intern-in-package-of-symbol
                                          (concatenate 'string name "-PACKAGE") 'acl2::x))))
                  :in-theory (e/d (bx-package-import-formula-p)
                                  (global-val assoc-equal known-package-alistp
                                   bx-world-theorem bx-package-items)))))))

(verify-guards bx-reserve-items)

(local
 (defthm bx-reserve-items-shape
   (implies (symbol-listp names)
            (bx-item-list-p (bx-reserve-items names wrld)))
   :hints (("Goal" :induct (bx-reserve-items names wrld)
            :in-theory (disable bx-reserve-kind-p)))))

; Each event supplies items and preserves the pending candidate table.
; The event walk either emits its items or adds them to that table.

(verify-guards bx-some-program-p)

(local
 (defthm bx-symbolp-of-symbol-list-head
   (implies (symbol-listp x) (symbolp (car x)))))

(local
 (defthm bx-symbol-names-of-function-and-fact-events
   (implies (and (bx-event-names-p ev)
                 (member-eq (bx-ev-type ev)
                            '(defun defuns defthm defaxiom defchoose encapsulate
                              defmacro defconst deflabel deftheory defstobj defabsstobj)))
            (symbol-listp (bx-names (bx-ev-namex ev))))
   :hints (("Goal" :in-theory (enable bx-event-names-p)))))

(defthm bx-event-definition-form
  (implies (and (bx-event-names-p ev)
                (member-eq (bx-ev-type ev) '(defun defuns)))
           (bx-defun-form-p (bx-ev-form ev)))
  :hints (("Goal" :in-theory (enable bx-event-names-p))))

(local
 (defthm bx-event-package-name
   (implies (and (bx-event-names-p ev) (eq (bx-ev-type ev) 'defpkg))
            (stringp (car (bx-names (bx-ev-namex ev)))))
   :hints (("Goal" :in-theory (enable bx-event-names-p)))))

(local
 (defthm bx-event-names-are-cons-or-nil
   (implies (bx-event-names-p ev)
            (iff (consp (bx-names (bx-ev-namex ev)))
                 (bx-names (bx-ev-namex ev))))
   :hints (("Goal" :use bx-true-listp-of-event-names))))

(local
 (defthm bx-event-functions-have-formals
   (implies (and (bx-event-data-p ev wrld)
                 (member-eq (bx-ev-type ev) '(defun defuns encapsulate)))
            (bx-functions-present-p (bx-names (bx-ev-namex ev)) wrld))
   :hints (("Goal" :in-theory (enable bx-event-data-p)))))

(local
 (defthm bx-owner-of-named-encapsulate
   (implies (and (bx-event-data-p ev wrld) (bx-event-names-p ev)
                 (eq (bx-ev-type ev) 'encapsulate)
                 (bx-names (bx-ev-namex ev)))
            (bx-constraint-owner-p (bx-constrainer ev wrld) wrld))
   :hints (("Goal" :use (bx-owner-of-bx-constrainer bx-event-data-entails-constraint)
            :in-theory (e/d (bx-event-data-p)
                            (bx-constrainer bx-owner-of-bx-constrainer
                             bx-event-data-entails-constraint))))))

(local
 (defthm bx-event-choice-has-input
   (implies (and (bx-event-data-p ev wrld)
                 (eq (bx-ev-type ev) 'defchoose)
                 (not (bx-constrained-p (car (bx-names (bx-ev-namex ev))) wrld)))
            (bx-choice-input-p (car (bx-names (bx-ev-namex ev))) wrld))
   :hints (("Goal" :in-theory (enable bx-event-data-p)))))

(local
 (in-theory (disable bx-program-defs bx-define-items bx-definition-candidates
                     bx-constrain-items bx-package-items bx-choose-items
                     bx-reserve-items bx-stobj-items bx-add-candidates
                     bx-constrainer bx-mentions-some bx-conjuncts
                     bx-all-program-p bx-some-program-p
                     bx-all-constrained-p bx-some-constrained-p
                     bx-formula-name bx-defs bx-rulers
                     bx-names-with-content bx-names-reserved bx-pending-p
                     bx-candidate-formulas bx-later-items bx-formula-cands
                     unknown-constraints-p)))

(verify-guards bx-event-items
  :hints (("Goal" :do-not-induct t)))

(local
 (defthm bx-event-items-shape
   (implies (and (bx-world-properties-p wrld)
                 (bx-event-data-p ev wrld) (bx-event-names-p ev)
                 (known-package-alistp
                  (getpropc 'known-package-alist 'global-value :missing wrld))
                 (symbolp encl)
                 (or (not encl) (bx-constraint-owner-p encl wrld))
                 (bx-pending-p pending wrld)
                 (bx-translations-p translations))
            (and (bx-item-list-p (car (bx-event-items ev encl pending defined
                                                      translations wrld)))
                 (bx-pending-p (mv-nth 1 (bx-event-items ev encl pending defined
                                                         translations wrld))
                               wrld)))
   :hints (("Goal" :do-not-induct t))))

(verify-guards bx-items
  :hints (("Goal"
           :use ((:instance bx-event-items-shape (ev (caar pairs)) (encl (cdar pairs)))
                 (:instance bx-item-listp-implies-true-listp
                            (x (car (bx-event-items (caar pairs) (cdar pairs)
                                                    pending defined translations wrld)))))
           :in-theory (disable bx-event-items bx-event-items-shape
                               bx-items-used bx-items-introduced bx-add-defined
                               bx-add-candidates bx-line-p bx-item-list-p)
           :do-not-induct t)))

(defthm bx-items-shape
  (implies (and (bx-world-properties-p wrld)
                (known-package-alistp
                 (getpropc 'known-package-alist 'global-value :missing wrld))
                (bx-enclosed-events-p pairs wrld) (bx-pending-p pending wrld)
                (bx-translations-p translations) (bx-item-list-p acc))
           (bx-item-list-p (bx-items pairs pending defined translations wrld acc)))
  :hints (("Goal" :induct (bx-items pairs pending defined translations wrld acc)
           :in-theory (disable bx-event-items bx-items-used bx-items-introduced
                               bx-add-defined bx-add-candidates bx-line-p))))

(defthm bx-enclose-inputs-of-event-range
  (implies (bx-export-world-p wrld)
           (and (bx-event-list-p (reverse (bx-events wrld lo hi nil)))
                (bx-event-constraints-p (reverse (bx-events wrld lo hi nil)) wrld)))
  :hints (("Goal" :in-theory (disable bx-events))))

(defthm bx-export-world-components
  (implies (bx-export-world-p wrld)
           (and (bx-world-properties-p wrld)
                (bx-event-world-p wrld)
                (known-package-alistp
                 (getpropc 'known-package-alist 'global-value :missing wrld))))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-empty-pending-table
  (bx-pending-p nil wrld)
  :hints (("Goal" :in-theory (enable bx-pending-p))))

(verify-guards bx-range-items
  :hints (("Goal" :in-theory (disable bx-items bx-enclose bx-events
                                     bx-event-constraints-p bx-enclosed-events-p
                                     bx-export-world-p reverse)
           :do-not-induct t)))

(defthm bx-range-items-shape
  (implies (and (bx-export-world-p wrld) (bx-translations-p translations))
           (bx-item-list-p (bx-range-items lo hi translations wrld)))
  :hints (("Goal" :in-theory (disable bx-items bx-enclose bx-events
                                     bx-enclosed-events-p bx-export-world-p reverse)
           :do-not-induct t)))
