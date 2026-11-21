(in-package "ACL2")

(include-book "structure-name-spelling")
(include-book "structure-coverage")

; A spelling has an owner in a constraint if its stem names the root or
; one of the root's siblings.  Count every selected record that could take
; the name, including an explicit use of the name in the event metadata.

(defun structure-unregistered-symbol-p (name wrld)
  (and name (symbolp name) (not (structure-registered-symbol-p name wrld))))

(defun structure-named-for-p (name owner)
  (and (symbolp owner)
       (equal (structure-name-source name) (structure-symbol-spelling owner))))

(defun structure-named-for-one-of-p (name owners)
  (and (consp owners)
       (or (structure-named-for-p name (car owners))
           (structure-named-for-one-of-p name (cdr owners)))))

(defun structure-name-from-constraint-p (name root wrld)
  (or (structure-named-for-p name root)
      (structure-named-for-one-of-p name (getpropc root 'siblings nil wrld))))

; A zero namex bypasses constraint conversion. The accepted tuple
; shapes also allow NIL, which has the scalar-symbol encoding here.

(defun structure-constraint-record-p (record)
  (and (eq (structure-event-kind record) 'encapsulate)
       (let ((namex (structure-event-namex record)))
         (or (null namex) (consp namex)))))

(defun structure-constraint-signature (record)
  (or (structure-event-namex record) '(nil)))

(defun structure-name-opportunity-p (name record wrld)
  (let ((kind (structure-event-kind record)))
    (cond ((structure-constraint-record-p record)
           (let ((root (structure-constraint-root record wrld)))
             (or (structure-name-from-constraint-p name root wrld)
                 (member-equal name (structure-constraint-signature record))
                 (member-equal name (getpropc root 'siblings nil wrld)))))
          ((eq kind 'defpkg)
           (equal name (structure-package-rule (structure-event-namex record))))
          ((member-eq kind '(defun defuns defchoose defthm defaxiom))
           (member-equal name (structure-event-names record)))
          (t nil))))

(defun structure-name-opportunities (name records wrld)
  (if (endp records)
      0
    (+ (if (structure-name-opportunity-p name (car records) wrld) 1 0)
       (structure-name-opportunities name (cdr records) wrld))))

(defun structure-naming-recordsp (records)
  (or (endp records)
      (and (structure-namex-shapep (car records))
           (structure-naming-recordsp (cdr records)))))

(local (in-theory (disable structure-event-kind structure-event-class structure-event-namex
                           structure-constraint-root structure-name-source structure-symbol-spelling
                           bx-formula-name fgetprop)))

; Pending formulas only carry an unregistered name for a constraint
; which could have made it.  Appending a bundle of items carries no
; formula candidate.

(defthm structure-ownership-passes-from-subset
  (implies (and (subsetp-equal a b) (structure-named-for-one-of-p name a))
           (structure-named-for-one-of-p name b))
  :hints (("Goal" :induct (subsetp-equal a b)
                  :in-theory (disable structure-named-for-p))))

(defthm structure-owner-in-sibling-list
  (implies (and (member-equal owner owners) (structure-named-for-p name owner))
           (structure-named-for-one-of-p name owners))
  :hints (("Goal" :induct (member-equal owner owners)
                  :in-theory (disable structure-named-for-p))))

(defthm structure-owner-of-definition-candidate
  (implies (and name (symbol-listp fns)
                (member-equal name (strip-cars (bx-definition-candidates fns wrld))))
           (structure-named-for-one-of-p name fns))
  :hints (("Goal" :induct (bx-definition-candidates fns wrld)
                  :in-theory (disable structure-named-for-p))
          ("Subgoal *1/2"
           :use ((:instance structure-definition-name-source (owner (car fns))))
           :in-theory (enable structure-named-for-p))))

(defun structure-pending-names-owned-p (name pending wrld)
  (or (endp pending)
      (and (or (not (member-equal name (strip-cars (bx-formula-cands (cdar pending)))))
               (structure-name-from-constraint-p name (caar pending) wrld))
           (structure-pending-names-owned-p name (cdr pending) wrld))))

(defthm structure-pending-name-at-owner
  (implies (and (structure-pending-names-owned-p name pending wrld)
                (member-equal name (strip-cars (bx-formula-cands (cdr (assoc-eq root pending))))))
           (structure-name-from-constraint-p name root wrld))
  :hints (("Goal" :induct (assoc-equal root pending)
                  :in-theory (disable bx-formula-cands structure-name-from-constraint-p))))

(defthm structure-pending-ownership-of-put-assoc
  (implies (and (structure-pending-names-owned-p name pending wrld)
                (or (not (member-equal name (strip-cars (bx-formula-cands candidates))))
                    (structure-name-from-constraint-p name root wrld)))
           (structure-pending-names-owned-p name (put-assoc-equal root candidates pending) wrld))
  :hints (("Goal" :in-theory (disable bx-formula-cands structure-name-from-constraint-p))))

(defthm structure-pending-ownership-of-add
  (implies (and (structure-pending-names-owned-p name pending wrld)
                (or (not (member-equal name (strip-cars (bx-formula-cands candidates))))
                    (structure-name-from-constraint-p name root wrld)))
           (structure-pending-names-owned-p name (bx-add-candidates root candidates pending) wrld))
  :hints (("Goal" :use ((:instance structure-pending-name-at-owner))
                  :in-theory (disable bx-formula-cands structure-name-from-constraint-p
                                      structure-pending-names-owned-p
                                      structure-pending-name-at-owner append))))

(defthm structure-unregistered-name-has-no-properties
  (implies (structure-unregistered-symbol-p name wrld)
           (and (not (bx-function-p name wrld))
                (not (bx-reserve-kind-p name wrld))
                (not (getpropc name 'theorem nil wrld))))
  :hints (("Goal" :in-theory (enable structure-registered-symbol-p structure-reserved-name-p))))

(local (in-theory (disable structure-unregistered-symbol-p structure-registered-symbol-p
                           structure-reserved-name-p)))

(defthm structure-unregistered-is-a-nonnil-symbol
  (implies (structure-unregistered-symbol-p name wrld)
           (and name (symbolp name)))
  :hints (("Goal" :in-theory (enable structure-unregistered-symbol-p)))
  :rule-classes :forward-chaining)

(defthm structure-namex-functions-are-symbols
  (implies (and (structure-namex-shapep record)
                (member-eq (structure-event-kind record) '(defun defuns defchoose)))
           (symbol-listp (bx-names (structure-event-namex record)))))

(defthm structure-head-of-symbol-list-is-a-symbol
  (implies (symbol-listp names) (symbolp (car names))))

(defthm structure-definition-candidates-are-formula-candidates
  (equal (bx-formula-cands (bx-definition-candidates fns wrld))
         (bx-definition-candidates fns wrld)))

(defthm structure-definitions-stay-with-their-owner
  (implies (and name (symbol-listp fns)
                (subsetp-equal fns (getpropc root 'siblings nil wrld))
                (structure-pending-names-owned-p name pending wrld))
           (structure-pending-names-owned-p
            name (bx-add-candidates root (bx-definition-candidates fns wrld) pending) wrld))
  :hints (("Goal"
           :use ((:instance structure-ownership-passes-from-subset
                            (a fns) (b (getpropc root 'siblings nil wrld))))
           :in-theory (disable bx-add-candidates bx-definition-candidates bx-formula-cands
                               subsetp-equal structure-pending-names-owned-p))))

(defthm structure-deferred-theorem-has-a-registered-name
  (implies (and (structure-unregistered-symbol-p name wrld)
                (bx-mentions-some (getpropc theorem 'theorem nil wrld) fns))
           (not (equal theorem name)))
  :hints (("Goal" :cases ((equal theorem name))))
  :rule-classes nil)

(defthm structure-choice-stays-with-its-owner
  (implies (and name
                (symbolp owner)
                (member-equal owner (getpropc root 'siblings nil wrld))
                (structure-pending-names-owned-p name pending wrld))
           (structure-pending-names-owned-p
            name (bx-add-candidates root
                                    (list (list (bx-formula-name owner "choice" wrld)
                                                :formula term))
                                    pending)
            wrld))
  :hints (("Goal"
           :cases ((equal name (bx-formula-name owner "choice" wrld)))
           :use ((:instance structure-choice-name-source)
                 (:instance structure-owner-in-sibling-list
                            (owners (getpropc root 'siblings nil wrld))))
           :in-theory (disable bx-add-candidates structure-pending-names-owned-p
                               structure-owner-in-sibling-list))))

(defthm structure-event-keeps-pending-ownership
  (implies (and (structure-unregistered-symbol-p name wrld)
                (structure-namex-shapep record)
                (structure-pending-names-owned-p name pending wrld))
           (structure-pending-names-owned-p
            name
            (mv-nth 1 (bx-event-items record enclosing pending defined translations wrld))
            wrld))
  :hints (("Goal"
           :use ((:instance structure-deferred-theorem-has-a-registered-name
                            (theorem (car (bx-names (structure-event-namex record))))
                            (fns (getpropc enclosing 'siblings nil wrld)))
                 (:instance structure-namex-functions-are-symbols))
           :in-theory (disable bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class bx-names
                               bx-add-candidates bx-all-program-p bx-some-program-p
                               bx-stobj-items bx-define-items bx-program-defs bx-choose-items
                               bx-constrain-items bx-reserve-items bx-package-items
                               bx-all-constrained-p bx-some-constrained-p bx-constrained-p
                               bx-definition-candidates bx-conjuncts bx-mentions-some constraint-info
                               bx-names-with-content bx-names-reserved subsetp-equal
                               bx-formula-name structure-pending-names-owned-p))))

(defthm structure-holding-items-keeps-pending-ownership
  (implies (structure-pending-names-owned-p name pending wrld)
           (structure-pending-names-owned-p
            name (bx-add-candidates root (list (list nil :after items)) pending) wrld))
  :hints (("Goal" :in-theory (disable bx-add-candidates structure-pending-names-owned-p))))

; The terms matched to candidates keep their names.  An unmatched
; conjunct gets a name based on the constraint root.

(defthm structure-candidate-term-names-come-from-input
  (implies (and (not (member-equal name (strip-cars candidates)))
                (not (member-equal name (strip-cars formulas))))
           (not (member-equal
                 name (strip-cars
                       (car (bx-candidate-terms candidates constraints root wrld
                                                formulas covered notes))))))
  :hints (("Goal" :induct (bx-candidate-terms candidates constraints root wrld
                                              formulas covered notes)
                  :in-theory (disable bx-equation-in bx-conjuncts union-equal reverse))))

(defthm structure-no-new-uncovered-name-without-owner
  (implies (and name (symbolp root) (natp position)
                (not (structure-named-for-p name root))
                (not (member-equal name (strip-cars formulas))))
           (not (member-equal name (strip-cars
                                    (car (bx-uncovered constraints covered root position
                                                       wrld formulas notes))))))
  :hints (("Goal" :induct (bx-uncovered constraints covered root position wrld formulas notes)
                  :in-theory (enable structure-position-word))
          ("Subgoal *1/2" :use ((:instance structure-position-name-source (owner root))))
          ("Subgoal *1/3" :use ((:instance structure-position-name-source (owner root))))))

(defthm structure-name-formulas-use-candidates-or-root
  (implies (and name (symbolp root)
                (not (member-equal name (strip-cars candidates)))
                (not (structure-named-for-p name root)))
           (not (member-equal name (strip-cars
                                    (car (bx-name-formulas constraints candidates root wrld))))))
  :hints (("Goal" :in-theory (disable bx-candidate-terms bx-uncovered
                                      structure-named-for-p))))

; Project just the statements which introduce the symbol in question.

(defun structure-name-items (name items)
  (cond ((endp items) nil)
        ((and (eq (caar items) :stmt) (structure-line-supplies-p name (cdar items)))
         (cons (cdar items) (structure-name-items name (cdr items))))
        (t (structure-name-items name (cdr items)))))

(defthm structure-name-items-of-append
  (equal (structure-name-items name (append a b))
         (append (structure-name-items name a) (structure-name-items name b)))
  :hints (("Goal" :in-theory (disable structure-line-supplies-p))))

(defthm structure-name-items-of-revappend
  (equal (structure-name-items name (revappend a b))
         (revappend (structure-name-items name a) (structure-name-items name b)))
  :hints (("Goal" :induct (revappend a b)
                  :in-theory (disable structure-line-supplies-p))))

(defthm structure-name-items-of-reverse
  (equal (structure-name-items name (reverse items))
         (reverse (structure-name-items name items)))
  :hints (("Goal" :in-theory (disable revappend structure-line-supplies-p))))

(defthm structure-name-items-is-true-list
  (true-listp (structure-name-items name items))
  :rule-classes :type-prescription)

; The accompanying items of these conversions are diagnostics.

(defthm structure-candidate-diagnostics-contain-no-statements
  (equal (structure-name-items
          name (mv-nth 2 (bx-candidate-terms candidates constraints root wrld
                                            formulas covered notes)))
         (reverse (structure-name-items name notes)))
  :hints (("Goal" :induct (bx-candidate-terms candidates constraints root wrld
                                              formulas covered notes)
                  :in-theory (disable bx-conjuncts bx-equation-in reverse union-equal))))

(defthm structure-uncovered-diagnostics-contain-no-statements
  (equal (structure-name-items
          name (mv-nth 1 (bx-uncovered constraints covered root position wrld formulas notes)))
         (reverse (structure-name-items name notes)))
  :hints (("Goal" :in-theory (disable reverse explode-nonnegative-integer))))

(defthm structure-formula-diagnostics-contain-no-statements
  (equal (structure-name-items
          name (mv-nth 1 (bx-name-formulas constraints candidates root wrld)))
         nil)
  :hints (("Goal" :in-theory (disable bx-uncovered bx-candidate-terms))))

(defthm structure-program-body-diagnostic-is-not-a-statement
  (not (equal (car (mv-nth 1 (bx-program-body fn form translations wrld))) :stmt))
  :hints (("Goal" :in-theory (disable bx-defun-forms))))

(defthm structure-program-diagnostics-contain-no-statements
  (equal (structure-name-items
          name (mv-nth 1 (bx-program-defs fns form translations wrld defs notes)))
         (reverse (structure-name-items name notes)))
  :hints (("Goal"
           :induct (bx-program-defs fns form translations wrld defs notes)
           :in-theory (disable bx-program-body bx-exec formals reverse))))

(defthm structure-matching-definition-is-one-line
  (implies (not (stringp name))
           (equal (structure-name-items name (bx-define-items fns wrld))
                  (if (member-equal name fns)
                      (list (list "define" (cons (bx-rulers (car fns) wrld)
                                                (bx-defs fns wrld))))
                    nil)))
  :hints (("Goal" :in-theory (disable bx-rulers bx-same-rulers bx-defs))))

(defthm structure-local-ready-contains-only-original-functions
  (implies (not (member-equal name todo))
           (not (member-equal name (bx-ready todo placed wrld))))
  :hints (("Goal" :induct (bx-ready todo placed wrld)
                  :in-theory (disable subsetp-equal intersection-equal all-fnnames1
                                      set-difference-equal))))

(defthm structure-local-order-contains-only-original-functions
  (implies (and (not (member-equal name todo)) (not (member-equal name acc)))
           (not (member-equal name (bx-local-order todo placed acc wrld fuel))))
  :hints (("Goal" :induct (bx-local-order todo placed acc wrld fuel)
                  :in-theory (disable bx-ready set-difference-equal reverse revappend))))

(defthm structure-no-stobj-definition-without-function
  (implies (and (not (stringp name)) (not (member-equal name fns)))
           (equal (structure-name-items name (bx-stobj-define-items fns wrld)) nil))
  :hints (("Goal" :in-theory (disable bx-define-items))))

(defthm structure-no-unregistered-stobj-name
  (implies (and (structure-unregistered-symbol-p name wrld)
                (not (stringp name))
                (not (member-equal name fns-acc))
                (not (structure-name-items name acc)))
           (equal (structure-name-items name (bx-stobj-items names defined fns-acc wrld acc))
                  nil))
  :hints (("Goal" :induct (bx-stobj-items names defined fns-acc wrld acc)
                  :in-theory (disable bx-ready bx-local-order bx-stobj-define-items
                                      bx-function-p bx-reserve-kind-p bx-exec bx-programp
                                      reverse revappend))))

(defthm structure-no-unregistered-reserve-name
  (implies (and (structure-unregistered-symbol-p name wrld)
                (not (stringp name)))
           (equal (structure-name-items name (bx-reserve-items names wrld)) nil))
  :hints (("Goal" :in-theory (disable bx-reserve-kind-p))))

; The primary items of a closing record exclude bundles being released.
; Every other event has only its own items.

(defun structure-signed-formula-table (root pending)
  (list (cons root (bx-formula-cands (cdr (assoc-eq root pending))))))

(defun structure-primary-items (record enclosing pending defined translations wrld)
  (if (structure-constraint-record-p record)
      (let ((root (structure-constraint-root record wrld)))
        (bx-constrain-items (structure-constraint-signature record) root
                            (structure-signed-formula-table root pending) wrld))
    (mv-let (items pending1)
      (bx-event-items record enclosing pending defined translations wrld)
      (declare (ignore pending1))
      items)))

(defthm structure-formula-candidates-have-no-later-items
  (equal (bx-later-items (bx-formula-cands candidates)) nil))

(defthm structure-formula-candidates-of-formula-candidates
  (equal (bx-formula-cands (bx-formula-cands candidates))
         (bx-formula-cands candidates)))

(local (defthm structure-associate-append
         (equal (append (append a b) c) (append a b c))))

(defthm structure-constraint-items-and-released-items
  (equal (bx-constrain-items names root pending wrld)
         (append (bx-constrain-items names root (structure-signed-formula-table root pending)
                                     wrld)
                 (bx-later-items (cdr (assoc-eq root pending)))))
  :hints (("Goal" :in-theory (disable bx-constrain-stmt bx-candidate-formulas
                                      bx-name-formulas bx-sort-by-event constraint-info
                                      bx-formula-cands bx-later-items set-difference-equal)))
  :rule-classes nil)

(defthm structure-event-name-items-breakdown
  (equal (structure-name-items
          name (car (bx-event-items record enclosing pending defined translations wrld)))
         (append (structure-name-items
                  name (structure-primary-items record enclosing pending defined
                                                translations wrld))
                 (and (structure-constraint-record-p record)
                      (structure-name-items
                       name
                       (bx-later-items
                        (cdr (assoc-eq (structure-constraint-root record wrld) pending)))))))
  :hints (("Goal"
           :use ((:instance structure-constraint-items-and-released-items
                            (names (structure-constraint-signature record))
                            (root (structure-constraint-root record wrld))))
           :in-theory (disable bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                               bx-constrainer bx-constrain-items bx-later-items
                               bx-all-program-p bx-some-program-p bx-program-defs
                               bx-all-constrained-p bx-some-constrained-p bx-definition-candidates
                               bx-add-candidates bx-define-items bx-choose-items bx-package-items
                               bx-stobj-items bx-reserve-items bx-names-with-content
                               bx-names-reserved bx-conjuncts bx-mentions-some constraint-info)))
  :rule-classes nil)

(defthm structure-signed-root-is-a-symbol
  (implies (and (structure-constraint-record-p record) (structure-namex-shapep record))
           (symbolp (structure-constraint-root record wrld)))
  :hints (("Goal" :in-theory (enable structure-constraint-root constraint-info))))

(defthm structure-constraint-outputs-at-most-one-matching-line
  (implies (not (stringp name))
           (<= (len (structure-name-items name (bx-constrain-stmt functions formulas wrld))) 1))
  :hints (("Goal" :in-theory (disable bx-arities remove-equal))))

(defthm structure-constraint-output-excludes-absent-name
  (implies (and (not (stringp name))
                (not (member-equal name functions))
                (not (member-equal name (strip-cars formulas))))
           (equal (structure-name-items name (bx-constrain-stmt functions formulas wrld)) nil))
  :hints (("Goal" :in-theory (disable bx-arities remove-equal))))

(defthm structure-no-owner-has-no-pending-name
  (implies (and (structure-pending-names-owned-p name pending wrld)
                (not (structure-name-from-constraint-p name root wrld)))
           (not (member-equal name (strip-cars (bx-formula-cands (cdr (assoc-eq root pending)))))))
  :hints (("Goal" :use ((:instance structure-pending-name-at-owner))
                  :in-theory (disable structure-name-from-constraint-p bx-formula-cands
                                      structure-pending-names-owned-p
                                      structure-pending-name-at-owner))))

(defthm structure-signed-primary-items-have-at-most-one-name-line
  (implies (not (stringp name))
           (<= (len (structure-name-items
                     name (bx-constrain-items names root
                                              (structure-signed-formula-table root pending)
                                              wrld)))
               1))
  :hints (("Goal" :in-theory (disable bx-constrain-stmt bx-name-formulas bx-candidate-formulas
                                      bx-sort-by-event constraint-info bx-formula-cands
                                      bx-later-items set-difference-equal))))

(defthm structure-signed-primary-items-require-possible-owner
  (implies (and name (not (stringp name)) (symbolp root)
                (structure-pending-names-owned-p name pending wrld)
                (not (structure-name-from-constraint-p name root wrld))
                (not (member-equal name names))
                (not (member-equal name (getpropc root 'siblings nil wrld))))
           (equal (structure-name-items
                   name (bx-constrain-items names root
                                            (structure-signed-formula-table root pending)
                                            wrld))
                  nil))
  :hints (("Goal"
           :use ((:instance structure-no-owner-has-no-pending-name))
           :in-theory (disable bx-constrain-stmt bx-name-formulas bx-candidate-formulas
                               bx-sort-by-event constraint-info bx-formula-cands
                               bx-later-items set-difference-equal structure-pending-names-owned-p
                               structure-no-owner-has-no-pending-name structure-named-for-p))))

(defthm structure-event-name-membership-for-nonnil-symbol
  (implies name
           (iff (member-equal name (bx-names (structure-event-namex record)))
                (member-equal name (structure-event-names record)))))

(defthm structure-singleton-namex
  (implies (or (symbolp namex) (stringp namex))
           (equal (car (bx-names namex)) namex)))

(defthm structure-symbol-namex-membership
  (implies (and name (symbolp (structure-event-namex record)))
           (iff (member-equal name (structure-event-names record))
                (equal name (structure-event-namex record)))))

(defthm structure-choice-name-items-are-single
  (<= (len (structure-name-items name (bx-choose-items fn wrld)))
      (if (equal name fn) 1 0))
  :hints (("Goal" :in-theory (disable bx-choose-parts bx-choose-axiom bx-choose-literal
                                      bx-beta formals))))

(defthm structure-package-name-items-are-single
  (implies (not (stringp name))
           (<= (len (structure-name-items name (bx-package-items package form wrld)))
               (if (equal name (structure-package-rule package)) 1 0)))
  :hints (("Goal" :in-theory (disable global-val
                                      structure-package-rule string-append))))

(defthm structure-choice-is-at-most-one-matching-line
  (<= (len (structure-name-items name (bx-choose-items fn wrld))) 1)
  :hints (("Goal" :use ((:instance structure-choice-name-items-are-single))
                  :in-theory (disable bx-choose-items structure-name-items
                                      structure-choice-name-items-are-single))))

(defthm structure-choice-only-supplies-its-function
  (implies (not (equal name fn))
           (equal (structure-name-items name (bx-choose-items fn wrld)) nil))
  :hints (("Goal" :use ((:instance structure-choice-name-items-are-single))
                  :in-theory (disable bx-choose-items structure-name-items
                                      structure-choice-name-items-are-single))))

(defthm structure-package-is-at-most-one-matching-line
  (implies (not (stringp name))
           (<= (len (structure-name-items name (bx-package-items package form wrld))) 1))
  :hints (("Goal" :use ((:instance structure-package-name-items-are-single))
                  :in-theory (disable bx-package-items structure-name-items
                                      structure-package-name-items-are-single structure-package-rule))))

(defthm structure-package-only-supplies-its-rule
  (implies (and (not (stringp name)) (not (equal name (structure-package-rule package))))
           (equal (structure-name-items name (bx-package-items package form wrld)) nil))
  :hints (("Goal" :use ((:instance structure-package-name-items-are-single))
                  :in-theory (disable bx-package-items structure-name-items
                                      structure-package-name-items-are-single structure-package-rule))))

(defthm structure-primary-items-are-limited-by-opportunity
  (implies (and (structure-unregistered-symbol-p name wrld)
                (structure-namex-shapep record)
                (structure-pending-names-owned-p name pending wrld))
           (<= (len (structure-name-items
                     name (structure-primary-items record enclosing pending defined
                                                   translations wrld)))
               (if (structure-name-opportunity-p name record wrld) 1 0)))
  :hints (("Goal"
           :in-theory (disable bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class bx-names
                               bx-add-candidates bx-all-program-p bx-some-program-p
                               bx-stobj-items bx-define-items bx-program-defs bx-choose-items
                               bx-constrain-items bx-reserve-items bx-package-items
                               bx-all-constrained-p bx-some-constrained-p bx-constrained-p
                               bx-definition-candidates bx-conjuncts constraint-info
                               bx-names-with-content bx-names-reserved subsetp-equal bx-formula-name
                               structure-pending-names-owned-p structure-event-names
                               structure-name-from-constraint-p structure-package-rule
                               structure-choice-name-items-are-single
                               structure-package-name-items-are-single bx-function-p
                               structure-nonempty-event-names structure-signed-formula-table))))
