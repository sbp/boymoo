(in-package "ACL2")

(include-book "faithful-choice")

; ACL2 stores the conjuncts of a known constraint. A formula can stand
; for its translated conjuncts, or for those conjuncts after ACL2's
; weak removal of guard holders with the removal lamp on.

(defund faithful-matching-conjuncts (formula stored)
  (let ((plain (flatten-ands-in-lit formula)))
    (if (subsetp-equal plain stored)
        plain
      (let ((without-holders
             (flatten-ands-in-lit (remove-guard-holders-weak formula t))))
        (if (subsetp-equal without-holders stored)
            without-holders
          :unmatched)))))

(defund faithful-flat-conjuncts-p (terms)
  (if (atom terms)
      (null terms)
    (and (equal (flatten-ands-in-lit (car terms)) (list (car terms)))
         (faithful-flat-conjuncts-p (cdr terms)))))

(defund faithful-formulas-match-p (formulas stored)
  (if (atom formulas)
      (null formulas)
    (and (not (eq (faithful-matching-conjuncts (cadar formulas) stored)
                  :unmatched))
         (faithful-formulas-match-p (cdr formulas) stored))))

(defund faithful-formulas-cover-term-p (term formulas stored)
  (if (endp formulas)
      nil
    (or (member-equal term (faithful-matching-conjuncts (cadar formulas) stored))
        (faithful-formulas-cover-term-p term (cdr formulas) stored))))

(defund faithful-formulas-cover-terms-p (terms formulas stored)
  (if (endp terms)
      t
    (and (faithful-formulas-cover-term-p (car terms) formulas stored)
         (faithful-formulas-cover-terms-p (cdr terms) formulas stored))))

(defund faithful-constraint-coverage-p (formulas stored)
  (and (faithful-formulas-match-p formulas stored)
       (faithful-formulas-cover-terms-p stored formulas stored)))

; These list rules track the formulas accumulated in reverse order.

(local
 (defthm faithful-member-of-union
   (iff (member-equal x (union-equal a b))
        (or (member-equal x a) (member-equal x b)))))

(local
 (defthm faithful-match-of-append
   (equal (faithful-formulas-match-p (append a b) stored)
          (and (faithful-formulas-match-p (true-list-fix a) stored)
               (faithful-formulas-match-p b stored)))
   :hints (("Goal" :in-theory (enable faithful-formulas-match-p)))))

(local
 (defthm faithful-match-of-true-list-fix
   (implies (faithful-formulas-match-p formulas stored)
            (faithful-formulas-match-p (true-list-fix formulas) stored))
   :hints (("Goal" :in-theory (enable faithful-formulas-match-p)))))

(local
 (defthm faithful-match-of-revappend
   (implies (and (faithful-formulas-match-p a stored)
                 (faithful-formulas-match-p b stored))
            (faithful-formulas-match-p (revappend a b) stored))
   :hints (("Goal" :induct (revappend a b)
            :in-theory (enable faithful-formulas-match-p)))))

(local
 (defthm faithful-match-of-reverse
   (implies (and (not (stringp formulas))
                 (faithful-formulas-match-p formulas stored))
            (faithful-formulas-match-p (reverse formulas) stored))
   :hints (("Goal" :in-theory (enable faithful-formulas-match-p reverse)))))

(local
 (defthm faithful-cover-of-append
   (iff (faithful-formulas-cover-term-p term (append a b) stored)
        (or (faithful-formulas-cover-term-p term a stored)
            (faithful-formulas-cover-term-p term b stored)))
   :hints (("Goal" :in-theory (enable faithful-formulas-cover-term-p)))))

(local
 (defthm faithful-cover-of-revappend
   (iff (faithful-formulas-cover-term-p term (revappend a b) stored)
        (or (faithful-formulas-cover-term-p term a stored)
            (faithful-formulas-cover-term-p term b stored)))
   :hints (("Goal" :induct (revappend a b)
            :in-theory (enable faithful-formulas-cover-term-p)))))

(local
 (defthm faithful-cover-of-reverse
   (implies (not (stringp formulas))
            (iff (faithful-formulas-cover-term-p term (reverse formulas) stored)
                 (faithful-formulas-cover-term-p term formulas stored)))
   :hints (("Goal" :in-theory (enable faithful-formulas-cover-term-p reverse)))))

; Matching a candidate adds only stored conjuncts to the set covered.
; The fallback for each remaining conjunct writes that conjunct itself.

(local
 (defthm faithful-bx-conjuncts-agree
   (equal (bx-conjuncts term stored)
          (let ((terms (faithful-matching-conjuncts term stored)))
            (if (eq terms :unmatched) :none terms)))
   :hints (("Goal" :in-theory (e/d (faithful-matching-conjuncts)
                                   (flatten-ands-in-lit
                                    remove-guard-holders-weak
                                    subsetp-equal))))))

(local
 (defthm faithful-candidate-terms-match
   (implies (faithful-formulas-match-p formulas stored)
            (faithful-formulas-match-p
             (car (bx-candidate-terms cands stored c wrld formulas covered notes))
             stored))
   :hints (("Goal"
            :induct (bx-candidate-terms cands stored c wrld formulas covered notes)
            :in-theory (e/d (faithful-formulas-match-p)
                            (bx-conjuncts bx-equation-in union-equal reverse))))))

(local
 (defthm faithful-candidate-terms-cover
   (implies (and (not (stringp formulas))
                 (implies (member-equal term covered)
                          (faithful-formulas-cover-term-p term formulas stored))
                 (member-equal term
                               (mv-nth 1
                                       (bx-candidate-terms cands stored c wrld
                                                           formulas covered notes))))
            (faithful-formulas-cover-term-p
             term (car (bx-candidate-terms cands stored c wrld formulas covered notes))
             stored))
   :hints (("Goal"
            :induct (bx-candidate-terms cands stored c wrld formulas covered notes)
            :in-theory (e/d (faithful-formulas-cover-term-p)
                            (bx-conjuncts bx-equation-in union-equal
                             reverse member-equal))))
   :rule-classes nil))

(local
 (defthm faithful-term-matches-itself
   (implies (and (equal (flatten-ands-in-lit term) (list term))
                 (member-equal term stored))
            (equal (faithful-matching-conjuncts term stored) (list term)))
   :hints (("Goal" :in-theory (e/d (faithful-matching-conjuncts)
                                   (flatten-ands-in-lit))))))

(local
 (defthm faithful-uncovered-terms-match
   (implies (and (faithful-flat-conjuncts-p remaining)
                 (subsetp-equal remaining stored)
                 (faithful-formulas-match-p formulas stored))
            (faithful-formulas-match-p
             (car (bx-uncovered remaining covered c i wrld formulas notes))
             stored))
   :hints (("Goal"
            :induct (bx-uncovered remaining covered c i wrld formulas notes)
            :in-theory (e/d (faithful-flat-conjuncts-p faithful-formulas-match-p)
                            (bx-formula-name flatten-ands-in-lit reverse))))))

(local
 (defthm faithful-uncovered-terms-cover
   (implies (and (faithful-flat-conjuncts-p remaining)
                 (subsetp-equal remaining stored)
                 (not (stringp formulas))
                 (or (faithful-formulas-cover-term-p term formulas stored)
                     (and (member-equal term remaining)
                          (not (member-equal term covered)))))
            (faithful-formulas-cover-term-p
             term (car (bx-uncovered remaining covered c i wrld formulas notes))
             stored))
   :hints (("Goal"
            :induct (bx-uncovered remaining covered c i wrld formulas notes)
            :in-theory (e/d (faithful-flat-conjuncts-p faithful-formulas-cover-term-p)
                            (bx-formula-name flatten-ands-in-lit reverse))))
   :rule-classes nil))

(local (include-book "std/lists/sets" :dir :system))

(local
 (defthm faithful-named-formulas-match
   (implies (faithful-flat-conjuncts-p stored)
            (faithful-formulas-match-p (car (bx-name-formulas stored cands c wrld))
                                       stored))
   :hints (("Goal"
            :in-theory (e/d (faithful-formulas-match-p)
                            (bx-candidate-terms bx-uncovered))))))

(local
 (defthm faithful-named-formulas-cover-one
   (implies (and (faithful-flat-conjuncts-p stored)
                 (member-equal term stored))
            (faithful-formulas-cover-term-p
             term (car (bx-name-formulas stored cands c wrld)) stored))
   :hints (("Goal"
            :use ((:instance faithful-candidate-terms-cover
                             (formulas nil) (covered nil) (notes nil))
                  (:instance faithful-uncovered-terms-cover
                             (remaining stored)
                             (covered (mv-nth 1 (bx-candidate-terms
                                                 cands stored c wrld nil nil nil)))
                             (i 1) (formulas nil) (notes nil)))
            :in-theory (e/d (faithful-formulas-cover-term-p)
                            (bx-candidate-terms bx-uncovered member-equal))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-named-formulas-cover-terms
   (implies (and (faithful-flat-conjuncts-p stored)
                 (subsetp-equal terms stored))
            (faithful-formulas-cover-terms-p
             terms (car (bx-name-formulas stored cands c wrld)) stored))
   :hints (("Goal"
            :induct (len terms)
            :in-theory (e/d (faithful-formulas-cover-terms-p) (bx-name-formulas)))
           ("Subgoal *1/1"
            :use ((:instance faithful-named-formulas-cover-one
                             (term (car terms))))))))

(defthm faithful-named-formulas-cover-constraint
  (implies (faithful-flat-conjuncts-p stored)
           (faithful-constraint-coverage-p
            (car (bx-name-formulas stored cands c wrld)) stored))
  :hints (("Goal"
           :in-theory (e/d (faithful-constraint-coverage-p) (bx-name-formulas)))))
