(in-package "ACL2")

(include-book "faithful-constraints")

; A generated label starts with the name of the function and the
; purpose of the formula. It can also carry a numeric suffix.

(defund faithful-label-stem (fn purpose)
  (concatenate 'string (symbol-name fn) " " purpose))

(defun faithful-label-variant-p (label base anchor index remaining)
  (declare (xargs :measure (nfix remaining)))
  (let ((spelling
         (if (equal index 0)
             base
           (concatenate 'string base " "
                        (coerce (explode-nonnegative-integer index 10 nil)
                                'string)))))
    (or (equal label (intern-in-package-of-symbol spelling anchor))
        (and (not (zp remaining))
             (faithful-label-variant-p label base anchor (+ 1 (nfix index))
                                       (- remaining 1))))))

(defund faithful-formula-label-p (label fn purpose)
  (and (equal (symbol-package-name label) (symbol-package-name fn))
       (faithful-label-variant-p label (faithful-label-stem fn purpose) fn 0 1000)))

; A generated label is usable only when it is a non-keyword symbol
; which has none of the world properties that put a name in use.

(defund faithful-name-in-use-p (name wrld)
  (or (not (eq (getprop name 'formals t 'current-acl2-world wrld) t))
      (getprop name 'theorem nil 'current-acl2-world wrld)
      (getprop name 'macro-body nil 'current-acl2-world wrld)
      (getprop name 'const nil 'current-acl2-world wrld)
      (getprop name 'label nil 'current-acl2-world wrld)
      (getprop name 'theory nil 'current-acl2-world wrld)
      (getprop name 'stobj nil 'current-acl2-world wrld)
      (getprop name 'stobj-live-var nil 'current-acl2-world wrld)))

(defund faithful-unused-formula-name-p (name wrld)
  (and name
       (symbolp name)
       (not (keywordp name))
       (not (faithful-name-in-use-p name wrld))))

(local
 (defthm faithful-bx-in-use-agrees
   (equal (bx-in-use-p name wrld) (faithful-name-in-use-p name wrld))
   :hints (("Goal" :in-theory (e/d (faithful-name-in-use-p) (fgetprop))))))

(local
 (defthm faithful-generated-label-variant
   (implies (bx-fresh-name base index anchor wrld fuel)
            (faithful-label-variant-p (bx-fresh-name base index anchor wrld fuel)
                                      base anchor index fuel))
   :hints (("Goal" :induct (bx-fresh-name base index anchor wrld fuel)
            :in-theory (disable bx-in-use-p explode-nonnegative-integer keywordp)))))

(local
 (defthm faithful-generated-label-unused
   (let ((name (bx-fresh-name base index anchor wrld fuel)))
     (implies name (faithful-unused-formula-name-p name wrld)))
   :hints (("Goal" :induct (bx-fresh-name base index anchor wrld fuel)
            :in-theory (e/d (faithful-unused-formula-name-p)
                            (bx-in-use-p explode-nonnegative-integer keywordp))))))

(local
 (defthm faithful-generated-label-in-anchor-package
   (let ((label (bx-fresh-name base index anchor wrld fuel)))
     (implies label
              (equal (symbol-package-name label) (symbol-package-name anchor))))
   :hints (("Goal" :induct (bx-fresh-name base index anchor wrld fuel)
            :in-theory (disable bx-in-use-p explode-nonnegative-integer keywordp)))))

(defthm faithful-formula-label-of-bx-name
  (let ((name (bx-formula-name fn purpose wrld)))
    (implies name
             (and (faithful-formula-label-p name fn purpose)
                  (faithful-unused-formula-name-p name wrld))))
  :hints (("Goal" :in-theory (e/d (faithful-formula-label-p faithful-label-stem)
                                  (bx-fresh-name faithful-label-variant-p)))))

; A choice label identifies a sibling function with the specified
; DEFCHOOSE-AXIOM. Theorem candidates use the name of their actual fact.

(defund faithful-recorded-choice-p (label axiom siblings wrld)
  (if (or (null axiom) (endp siblings))
      nil
    (let ((fn (car siblings)))
      (or (and (equal axiom (getprop fn 'defchoose-axiom nil 'current-acl2-world wrld))
               (faithful-formula-label-p label fn "choice"))
          (faithful-recorded-choice-p label axiom (cdr siblings) wrld)))))

(defund faithful-formula-mentions-sibling-p (formula owner wrld)
  (intersectp-eq (all-fnnames formula) (faithful-constraint-siblings owner wrld)))

(defun faithful-candidate-p (candidate owner wrld)
  (let ((name (car candidate))
        (data (caddr candidate))
        (siblings (faithful-constraint-siblings owner wrld)))
    (case (cadr candidate)
      (:formula
       (and data
            (or (null name)
                (and (equal data (getprop name 'theorem nil 'current-acl2-world wrld))
                     (faithful-formula-mentions-sibling-p data owner wrld))
                (and (faithful-unused-formula-name-p name wrld)
                     (faithful-recorded-choice-p name data siblings wrld)))))
      (:definition
       (and (member-equal data siblings)
            (or (null name)
                (and (faithful-unused-formula-name-p name wrld)
                     (faithful-formula-label-p name data "definition")))))
      (otherwise nil))))

(defun faithful-candidates-p (candidates owner wrld)
  (if (endp candidates)
      t
    (and (faithful-candidate-p (car candidates) owner wrld)
         (faithful-candidates-p (cdr candidates) owner wrld))))

(defun faithful-pending-candidates-p (pending wrld)
  (if (endp pending)
      t
    (and (faithful-candidates-p (bx-formula-cands (cdar pending))
                               (caar pending) wrld)
         (faithful-pending-candidates-p (cdr pending) wrld))))

(local
 (defthm faithful-empty-candidates
   (faithful-candidates-p nil owner wrld)
   :hints (("Goal" :expand ((faithful-candidates-p nil owner wrld))))))

(defthm faithful-pending-lookup
  (implies (faithful-pending-candidates-p pending wrld)
           (faithful-candidates-p (bx-formula-cands (cdr (assoc-equal owner pending)))
                                  owner wrld))
  :hints (("Goal" :induct (faithful-pending-candidates-p pending wrld)
           :in-theory (disable faithful-candidates-p bx-formula-cands))))

(local
 (defthm faithful-candidates-of-append
   (equal (faithful-candidates-p (append a b) owner wrld)
          (and (faithful-candidates-p a owner wrld)
               (faithful-candidates-p b owner wrld)))
   :hints (("Goal" :in-theory (disable faithful-candidate-p)))))

(local
 (defthm faithful-formula-cands-of-append
   (equal (bx-formula-cands (append a b))
          (append (bx-formula-cands a) (bx-formula-cands b)))))

(local
 (defthm faithful-pending-of-put-assoc
   (implies (and (faithful-pending-candidates-p pending wrld)
                 (faithful-candidates-p (bx-formula-cands cands) owner wrld))
            (faithful-pending-candidates-p (put-assoc-equal owner cands pending)
                                           wrld))
   :hints (("Goal" :induct (put-assoc-equal owner cands pending)
            :in-theory (disable faithful-candidates-p bx-formula-cands)))))

(local
 (defthm faithful-pending-of-bx-add-candidates
   (implies (and (faithful-pending-candidates-p pending wrld)
                 (faithful-candidates-p (bx-formula-cands cands) owner wrld))
            (faithful-pending-candidates-p (bx-add-candidates owner cands pending)
                                           wrld))
   :hints (("Goal" :in-theory (disable faithful-pending-candidates-p
                                       faithful-candidates-p put-assoc-equal
                                       bx-formula-cands)))))

(local (include-book "std/lists/sets" :dir :system))

(local
 (defthm faithful-definition-candidates-have-sources
   (implies (subsetp-equal fns (faithful-constraint-siblings owner wrld))
            (faithful-candidates-p (bx-formula-cands
                                     (bx-definition-candidates fns wrld))
                                    owner wrld))
   :hints (("Goal" :in-theory (disable bx-formula-name)))))

(local
 (defthm faithful-choice-from-sibling
   (implies (and axiom
                 (member-equal fn siblings)
                 (equal axiom (getprop fn 'defchoose-axiom nil 'current-acl2-world wrld))
                 (faithful-formula-label-p label fn "choice"))
            (faithful-recorded-choice-p label axiom siblings wrld))
   :hints (("Goal" :induct (member-equal fn siblings)
            :in-theory (e/d (faithful-recorded-choice-p) (fgetprop))))
   :rule-classes nil))

(local
 (defthm faithful-choice-candidate-has-source
   (let ((axiom (getprop fn 'defchoose-axiom nil 'current-acl2-world wrld)))
     (implies (and axiom (member-equal fn (faithful-constraint-siblings owner wrld)))
              (faithful-candidate-p
               (list (bx-formula-name fn "choice" wrld) :formula axiom)
               owner wrld)))
   :hints (("Goal"
            :use ((:instance faithful-choice-from-sibling
                             (axiom (getprop fn 'defchoose-axiom nil 'current-acl2-world wrld))
                             (siblings (faithful-constraint-siblings owner wrld))
                             (label (bx-formula-name fn "choice" wrld))))
            :in-theory (disable bx-formula-name fgetprop)))))

(local
 (defthm faithful-candidates-of-event
   (implies (and (faithful-fact-event-record-p ev wrld)
                 (faithful-pending-candidates-p pending wrld))
            (faithful-pending-candidates-p
             (mv-nth 1 (bx-event-items ev encl pending defined translations wrld))
             wrld))
   :hints (("Goal"
            :use ((:instance faithful-event-type-reader (event ev))
                  (:instance faithful-event-name-reader (event ev)))
            :in-theory (e/d (faithful-fact-event-record-p faithful-constraint-siblings
                             faithful-formula-mentions-sibling-p)
                            (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                             access-event-tuple-type faithful-event-names bx-names
                             bx-programp bx-all-program-p bx-some-program-p
                             bx-constrained-p bx-all-constrained-p
                             bx-some-constrained-p bx-program-defs bx-define-items
                             bx-add-candidates bx-definition-candidates
                             bx-constrainer bx-stobj-items fgetprop bx-conjuncts
                             constraint-info bx-choose-items
                             bx-constrain-items bx-package-items bx-formula-name
                             bx-reserve-items bx-names-with-content bx-names-reserved
                             faithful-pending-candidates-p faithful-recorded-choice-p))
            :do-not-induct t))))

(local
 (defthm faithful-candidates-of-next-pending
   (implies (faithful-pending-candidates-p pending wrld)
            (faithful-pending-candidates-p
             (faithful-next-pending encl items pending wrld)
             wrld))
   :hints (("Goal" :in-theory (e/d (faithful-next-pending)
                                   (bx-add-candidates faithful-pending-candidates-p))))))

; An originating event sees only candidates accumulated from events
; whose fact records are present.

(local
 (defun faithful-missing-fact (events wrld)
   (if (endp events)
       nil
     (if (faithful-fact-event-record-p (car events) wrld)
         (faithful-missing-fact (cdr events) wrld)
       (list (car events))))))

(local
 (defthm faithful-missing-fact-is-event
   (implies (faithful-missing-fact events wrld)
            (and (member-equal (car (faithful-missing-fact events wrld)) events)
                 (not (faithful-fact-event-record-p
                       (car (faithful-missing-fact events wrld))
                       wrld))))
   :hints (("Goal" :induct (faithful-missing-fact events wrld)))
   :rule-classes nil))

(local
 (defthm faithful-no-missing-fact-in-range
   (implies (faithful-fact-world-p wrld)
            (not (faithful-missing-fact
                  (strip-cars
                   (bx-enclose (reverse (bx-events wrld lo hi nil)) nil nil wrld))
                  wrld)))
   :hints (("Goal"
            :use ((:instance faithful-event-landmark-of-range
                             (event (car (faithful-missing-fact
                                          (strip-cars (bx-enclose
                                                       (reverse (bx-events wrld lo hi nil))
                                                       nil nil wrld))
                                          wrld))))
                  (:instance faithful-fact-record-from-world
                             (event (car (faithful-missing-fact
                                          (strip-cars (bx-enclose
                                                       (reverse (bx-events wrld lo hi nil))
                                                       nil nil wrld))
                                          wrld))))
                  (:instance faithful-missing-fact-is-event
                             (events (strip-cars (bx-enclose
                                                  (reverse (bx-events wrld lo hi nil))
                                                  nil nil wrld)))))
            :in-theory (disable bx-events bx-enclose faithful-missing-fact)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-pending-of-item-origin
   (implies (and (not (faithful-missing-fact (strip-cars pairs) wrld))
                 (faithful-pending-candidates-p pending wrld))
            (faithful-pending-candidates-p
             (caddr (faithful-item-origin item pairs pending defined
                                          translations wrld))
             wrld))
   :hints (("Goal"
            :induct (faithful-item-origin item pairs pending defined translations wrld)
            :in-theory (disable bx-event-items bx-add-defined member-equal)))
   :rule-classes nil))

(defthm faithful-pending-of-statement-origin
  (implies (faithful-fact-world-p wrld)
           (faithful-pending-candidates-p
            (caddr (faithful-statement-origin line lo hi translations wrld))
            wrld))
  :hints (("Goal"
           :use (faithful-no-missing-fact-in-range
                 (:instance faithful-pending-of-item-origin
                            (item (cons :stmt line))
                            (pairs (bx-enclose (reverse (bx-events wrld lo hi nil))
                                               nil nil wrld))
                            (pending nil) (defined nil)))
           :in-theory (e/d (faithful-statement-origin)
                           (faithful-item-origin bx-events bx-enclose
                            faithful-missing-fact))
           :do-not-induct t))
  :rule-classes nil)
