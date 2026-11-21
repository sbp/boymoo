(in-package "ACL2")

(include-book "faithful-candidates")

; A labeled equation identifies a function and its formals. When ACL2
; marks a constraint unknown, the equation uses the stored body.

(defun faithful-first-defining-equation (fn formals conjuncts)
  (if (endp conjuncts)
      nil
    (let ((term (car conjuncts)))
      (if (case-match term
            (('equal (!fn . actuals) &) (equal actuals formals))
            (& nil))
          term
        (faithful-first-defining-equation fn formals (cdr conjuncts))))))

(defund faithful-labeled-equation-p (name term stored owner wrld)
  (case-match term
    (('equal (fn . formals) body)
     (and (member-equal fn (faithful-constraint-siblings owner wrld))
          (faithful-formula-label-p name fn "definition")
          (equal formals (getprop fn 'formals nil 'current-acl2-world wrld))
          (if (unknown-constraints-p stored)
              (equal body (getprop fn 'unnormalized-body nil 'current-acl2-world wrld))
            (equal term (faithful-first-defining-equation fn formals stored)))))
    (& nil)))

(defund faithful-conjunct-label-purpose (position)
  (concatenate 'string "constraint "
               (coerce (explode-nonnegative-integer position 10 nil) 'string)))

(defun faithful-indexed-conjunct-p (name term conjuncts owner position)
  (if (endp conjuncts)
      nil
    (or (and (equal term (car conjuncts))
             (faithful-formula-label-p name owner
                                       (faithful-conjunct-label-purpose position)))
        (faithful-indexed-conjunct-p name term (cdr conjuncts) owner
                                     (+ 1 position)))))

(defund faithful-constraint-formula-p (pair stored owner wrld)
  (case-match pair
    ((name term)
     (and name
          (or (and term
                   (faithful-formula-data-p pair wrld)
                   (faithful-formula-mentions-sibling-p term owner wrld))
              (and (faithful-unused-formula-name-p name wrld)
                   (or (faithful-recorded-choice-p
                        name term (faithful-constraint-siblings owner wrld) wrld)
                       (if (unknown-constraints-p stored)
                           (faithful-labeled-equation-p name term stored owner wrld)
                         (or (and (member-equal term stored)
                                  (faithful-labeled-equation-p name term stored owner wrld))
                             (faithful-indexed-conjunct-p name term stored owner 1))))))))
    (& nil)))

; A candidate produces a stored fact, a stored choice axiom, or the
; equation it finds in the recorded constraint.

(local
 (defthm faithful-unused-name-has-no-fact
   (implies (faithful-unused-formula-name-p name wrld)
            (not (getprop name 'theorem nil 'current-acl2-world wrld)))
   :hints (("Goal" :in-theory (e/d (faithful-unused-formula-name-p
                                    faithful-name-in-use-p)
                                   (fgetprop))))))

(local
 (defthm faithful-equation-in-stored-constraint
   (implies (bx-equation-in fn stored wrld)
            (member-equal (bx-equation-in fn stored wrld) stored))
   :hints (("Goal" :in-theory (disable formals)))))

(local
 (defthm faithful-first-equation-agrees
   (implies (plist-worldp-with-formals wrld)
            (equal (faithful-first-defining-equation
                    fn (getprop fn 'formals nil 'current-acl2-world wrld) stored)
                   (bx-equation-in fn stored wrld)))
   :hints (("Goal" :induct (bx-equation-in fn stored wrld)
            :in-theory (disable formals fgetprop plist-worldp-with-formals)))))

(local
 (defthm faithful-shape-of-bx-equation-in
   (let ((term (bx-equation-in fn stored wrld)))
     (implies term
              (equal term (list 'equal (cons fn (formals fn wrld)) (caddr term)))))
   :hints (("Goal" :induct (bx-equation-in fn stored wrld)
            :in-theory (disable formals fgetprop)))
   :rule-classes nil))

(local
 (defthm faithful-equation-of-bx-equation-in
   (implies (and (plist-worldp-with-formals wrld)
                 (not (unknown-constraints-p stored))
                 (faithful-formula-label-p name fn "definition")
                 (member-equal fn (faithful-constraint-siblings owner wrld))
                 (bx-equation-in fn stored wrld))
            (faithful-labeled-equation-p
             name (bx-equation-in fn stored wrld) stored owner wrld))
   :hints (("Goal" :use faithful-shape-of-bx-equation-in
            :in-theory (e/d (faithful-labeled-equation-p)
                            (bx-equation-in fgetprop formals plist-worldp-with-formals
                             unknown-constraints-p faithful-first-defining-equation))))))

(local
 (defthm faithful-candidate-formula-in-known-constraint
   (let ((term (if (eq (cadr cand) :formula)
                   (caddr cand)
                 (bx-equation-in (caddr cand) stored wrld))))
     (implies (and (plist-worldp-with-formals wrld)
                   (not (unknown-constraints-p stored))
                   (faithful-candidate-p cand owner wrld)
                   (car cand)
                   term)
              (faithful-constraint-formula-p (list (car cand) term)
                                             stored owner wrld)))
   :hints (("Goal"
            :in-theory (e/d (faithful-constraint-formula-p faithful-formula-data-p)
                            (bx-equation-in formals fgetprop
                             plist-worldp-with-formals))))
   :rule-classes nil))

(local
 (defthm faithful-candidate-terms-sources
   (implies (and (plist-worldp-with-formals wrld)
                 (faithful-candidates-p cands owner wrld)
                 (not (unknown-constraints-p stored))
                 (car pair)
                 (not (stringp formulas))
                 (not (member-equal pair formulas))
                 (member-equal pair (car (bx-candidate-terms
                                          cands stored owner wrld formulas covered
                                          notes))))
            (faithful-constraint-formula-p pair stored owner wrld))
   :hints (("Goal"
            :induct (bx-candidate-terms cands stored owner wrld formulas covered notes)
            :in-theory (disable bx-equation-in bx-conjuncts union-equal
                                faithful-candidate-p plist-worldp-with-formals
                                unknown-constraints-p))
           ("Subgoal *1/3"
            :use ((:instance faithful-candidate-formula-in-known-constraint
                             (cand (car cands))))))
   :rule-classes nil))

; Formulas written from the uncovered part of the stored constraint
; carry their position in that constraint.

(local
 (defthm faithful-uncovered-pair-has-index
   (implies (and (not (stringp formulas))
                 (car pair)
                 (not (member-equal pair formulas))
                 (member-equal pair (car (bx-uncovered
                                          remaining covered owner position
                                          wrld formulas notes))))
            (and (equal pair (list (car pair) (cadr pair)))
                 (faithful-unused-formula-name-p (car pair) wrld)
                 (faithful-indexed-conjunct-p (car pair) (cadr pair) remaining
                                              owner position)))
   :hints (("Goal"
            :induct (bx-uncovered remaining covered owner position wrld formulas notes)
            :in-theory (e/d (faithful-conjunct-label-purpose)
                            (bx-formula-name explode-nonnegative-integer))))
   :rule-classes nil))

(local
 (defthm faithful-named-formula-in-known-constraint
   (implies (and (plist-worldp-with-formals wrld)
                 (faithful-candidates-p cands owner wrld)
                 (not (unknown-constraints-p stored))
                 (car pair)
                 (member-equal pair (car (bx-name-formulas stored cands owner wrld))))
            (faithful-constraint-formula-p pair stored owner wrld))
   :hints (("Goal"
            :use ((:instance faithful-candidate-terms-sources
                             (formulas nil) (covered nil) (notes nil))
                  (:instance faithful-uncovered-pair-has-index
                             (remaining stored) (position 1)
                             (covered (mv-nth 1 (bx-candidate-terms
                                                 cands stored owner wrld nil nil nil)))
                             (formulas nil) (notes nil)))
            :in-theory (e/d (faithful-constraint-formula-p)
                            (bx-candidate-terms bx-uncovered
                             faithful-candidates-p plist-worldp-with-formals
                             faithful-indexed-conjunct-p))
            :do-not-induct t))))

; Where there is no recorded list, each selected candidate still has the
; formula of a named fact, a choice axiom, or a stored definition.

(local
 (defthm faithful-candidate-formula-in-unknown-constraint
   (let* ((fn (caddr cand))
          (term (if (eq (cadr cand) :formula)
                    fn
                  (list 'equal (cons fn (formals fn wrld))
                        (getprop fn 'unnormalized-body nil 'current-acl2-world wrld)))))
     (implies (and (plist-worldp-with-formals wrld)
                   (unknown-constraints-p stored)
                   (faithful-candidate-p cand owner wrld)
                   (car cand))
              (faithful-constraint-formula-p (list (car cand) term)
                                             stored owner wrld)))
   :hints (("Goal"
            :in-theory (e/d (faithful-constraint-formula-p faithful-formula-data-p
                             faithful-labeled-equation-p)
                            (formals fgetprop plist-worldp-with-formals))))))

(local
 (defthm faithful-named-formula-in-unknown-constraint
   (implies (and (plist-worldp-with-formals wrld)
                 (faithful-candidates-p cands owner wrld)
                 (unknown-constraints-p stored)
                 (car pair)
                 (member-equal pair (bx-candidate-formulas cands wrld)))
            (faithful-constraint-formula-p pair stored owner wrld))
   :hints (("Goal"
            :induct (bx-candidate-formulas cands wrld)
            :in-theory (disable formals fgetprop plist-worldp-with-formals
                                faithful-candidate-p
                                faithful-candidate-formula-in-unknown-constraint))
           ("Subgoal *1/2"
            :use ((:instance faithful-candidate-formula-in-unknown-constraint
                             (cand (car cands))))))))

; Use the pending candidates of the originating encapsulate. The first
; listed function comes from its signature and identifies the constraint.

(local
 (defthm faithful-first-function-of-arities
   (equal (caar (bx-arities fns wrld)) (car fns))
   :hints (("Goal" :in-theory (disable formals)))))

(defund faithful-constraint-formula-from-world-p (pair args wrld)
  (let* ((fn (caaar args))
         (owner (faithful-constraint-owner fn wrld)))
    (faithful-constraint-formula-p pair (faithful-stored-constraint owner wrld)
                                   owner wrld)))

(local
 (defthm faithful-formula-label-present
   (implies (and (not (member-equal nil (strip-cars formulas)))
                 (member-equal pair formulas))
            (car pair))))

(local
 (defthm faithful-constraint-formula-of-items
   (implies (and (plist-worldp-with-formals wrld)
                 (consp signature)
                 (equal owner (faithful-constraint-owner (car signature) wrld))
                 (faithful-pending-candidates-p pending wrld)
                 (member-equal (cons :stmt line)
                               (faithful-direct-constrain-items signature owner pending wrld))
                 (member-equal pair (cadr (cadr line))))
            (faithful-constraint-formula-from-world-p pair (cadr line) wrld))
   :hints (("Goal"
            :use faithful-pending-lookup
            :in-theory (e/d (faithful-direct-constrain-items
                             faithful-constraint-formula-from-world-p
                             faithful-stored-constraint)
                            (faithful-formula-pending bx-formula-cands bx-later-items
                             bx-sort-by-event bx-arities bx-name-formulas bx-candidate-formulas
                             constraint-info fgetprop
                             faithful-pending-candidates-p faithful-candidates-p
                             faithful-pending-lookup plist-worldp-with-formals))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-constraint-formula-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (equal (car line) "constrain")
                   (member-equal pair (cadr (cadr line)))
                   (plist-worldp-with-formals wrld)
                   (faithful-constraint-world-p wrld)
                   (faithful-fact-world-p wrld)
                   origin)
              (faithful-constraint-formula-from-world-p pair (cadr line) wrld)))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  faithful-landmark-of-statement-origin
                  faithful-pending-of-statement-origin
                  (:instance faithful-constraint-items-of-event
                             (ev (car (faithful-statement-origin
                                       line lo hi translations wrld)))
                             (encl (cadr (faithful-statement-origin
                                         line lo hi translations wrld)))
                             (pending (caddr (faithful-statement-origin
                                             line lo hi translations wrld)))
                             (defined (cadddr (faithful-statement-origin
                                               line lo hi translations wrld))))
                  (:instance faithful-constraint-formula-of-items
                             (signature (faithful-event-names
                                         (car (faithful-statement-origin
                                               line lo hi translations wrld))))
                             (owner (faithful-constraint-owner
                                     (car (faithful-event-names
                                           (car (faithful-statement-origin
                                                 line lo hi translations wrld))))
                                     wrld))
                             (pending (caddr (faithful-statement-origin
                                              line lo hi translations wrld)))))
            :in-theory (disable bx-event-items bx-constrain-items
                                faithful-event-names
                                faithful-pending-candidates-p plist-worldp-with-formals)
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-constrain-formula-source
  (implies
   (and (equal (car line) "constrain")
        (member-equal pair (cadr (cadr line)))
        (plist-worldp-with-formals wrld)
        (faithful-constraint-world-p wrld)
        (faithful-fact-world-p wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-constraint-formula-from-world-p pair (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-constraint-formula-of-origin (lo 0))
                 faithful-constraint-formula-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

; A formula under a name already in use in ACL2 must be the fact of
; that very name. Generated names have none of the properties of a
; name in use.

(defthm faithful-constrain-name-in-use
  (implies
   (and (equal (car line) "constrain")
        (member-equal pair (cadr (cadr line)))
        (faithful-name-in-use-p (car pair) wrld)
        (plist-worldp-with-formals wrld)
        (faithful-constraint-world-p wrld)
        (faithful-fact-world-p wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir cbd wrld)))))
   (and (getprop (car pair) 'theorem nil 'current-acl2-world wrld)
        (equal pair
               (list (car pair)
                     (getprop (car pair) 'theorem nil 'current-acl2-world wrld)))))
  :hints (("Goal"
           :use faithful-constrain-formula-source
           :in-theory (e/d (faithful-constraint-formula-from-world-p
                            faithful-constraint-formula-p faithful-formula-data-p
                            faithful-unused-formula-name-p)
                           (bx-library-lines bx-book-lines fgetprop
                            unknown-constraints-p faithful-indexed-conjunct-p
                            plist-worldp-with-formals))
           :do-not-induct t))
  :rule-classes nil)
