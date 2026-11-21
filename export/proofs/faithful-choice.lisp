(in-package "ACL2")

(include-book "faithful-packages")

; Build the literal of spec/logic.md, section 6. ACL2's SUBCOR-VAR
; substitutes actuals for corresponding variables in a translated term.

(defun faithful-choice-projections (bound call index)
  (if (endp bound)
      nil
    (cons (list 'mv-nth (list 'quote index) call)
          (faithful-choice-projections (cdr bound) call (+ 1 index)))))

(defun faithful-choice-substitutes (bound call)
  (if (cdr bound)
      (faithful-choice-projections bound call 0)
    (list call)))

(defund faithful-choice-literal (fn bound free body free2 strengthened)
  (let* ((call (cons fn free))
         (actuals (faithful-choice-substitutes bound call))
         (instance (subcor-var bound actuals body))
         (implication (list 'implies body instance))
         (basic (if (cdr bound)
                    (list 'if (list 'true-listp call) implication ''nil)
                  implication)))
    (if (not strengthened)
        basic
      (let* ((call2 (cons fn free2))
             (actuals2 (faithful-choice-substitutes bound call2))
             (body2 (subcor-var free free2 body))
             (equal-values (list 'equal call call2))
             (first-distinguishes
              (list 'if instance
                    (list 'not (subcor-var bound actuals body2))
                    ''nil))
             (second-distinguishes
              (list 'if (subcor-var bound actuals2 body2)
                    (list 'not (subcor-var bound actuals2 body))
                    ''nil)))
        (list 'if basic
              (list 'if equal-values equal-values
                    (list 'if first-distinguishes first-distinguishes
                          second-distinguishes))
              ''nil)))))

(defund faithful-choice-axiom (fn bound free body free2)
  (faithful-choice-literal fn bound free body free2 (not (null free2))))

; Expand applications of closed lambdas by putting their reduced
; actuals for their formals. Quotes are left intact. This is syntactic
; beta reduction, with no evaluation of primitive calls.

(defun faithful-beta-reduce (expression bindings arguments-p)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   (arguments-p
    (if (consp expression)
        (cons (faithful-beta-reduce (car expression) bindings nil)
              (faithful-beta-reduce (cdr expression) bindings t))
      nil))
   ((atom expression)
    (let ((binding (assoc-equal expression bindings)))
      (if binding (cdr binding) expression)))
   ((eq (car expression) 'quote) expression)
   (t (let ((operator (car expression))
            (actuals (faithful-beta-reduce (cdr expression) bindings t)))
        (if (consp operator)
            (faithful-beta-reduce (caddr operator)
                                  (pairlis$ (cadr operator) actuals)
                                  nil)
          (cons operator actuals))))))

(defund faithful-beta-normal-form (term)
  (faithful-beta-reduce term nil nil))

; Section 6 of spec/logic.md gives the basic axiom for a nullary line.
; ACL2 can record the strengthened axiom with both calls equal to (FN);
; its additional conjunct is then true by reflexivity.

(defund faithful-choice-data-p (args wrld)
  (let* ((fn (car args))
         (bound (cadr args))
         (free (caddr args))
         (body (cadddr args))
         (free2 (car (cddddr args)))
         (axiom (getprop fn 'defchoose-axiom nil 'current-acl2-world wrld))
         (stored (faithful-beta-normal-form axiom)))
    (and (equal args (list fn bound free body free2))
         (consp bound)
         axiom
         (equal free (getprop fn 'formals nil 'current-acl2-world wrld))
         (or (equal stored (faithful-beta-normal-form
                            (faithful-choice-axiom fn bound free body free2)))
             (and (null free)
                  (null free2)
                  (equal stored (faithful-beta-normal-form
                                 (faithful-choice-literal fn bound nil body nil t))))))))

; Compare the independent construction and beta reduction with the two
; expressions tested by the statement constructor.

(local
 (defthm faithful-choice-projections-of-bx
   (implies (natp index)
            (equal (bx-mv-nths (+ index (len bound)) index call)
                   (faithful-choice-projections bound call index)))
   :hints (("Goal" :induct (faithful-choice-projections bound call index))
           ("Subgoal *1/1" :expand ((bx-mv-nths index index call))))))

(local
 (defthm faithful-choice-projections-from-zero
   (equal (bx-mv-nths (len bound) 0 call)
          (faithful-choice-projections bound call 0))
   :hints (("Goal" :use ((:instance faithful-choice-projections-of-bx (index 0)))
            :in-theory (disable len bx-mv-nths faithful-choice-projections)))))

(local
 (defthm faithful-choice-literal-of-bx
   (equal (bx-choose-literal fn bound free body free2 strengthened)
          (faithful-choice-literal fn bound free body free2 strengthened))
   :hints (("Goal"
            :in-theory (e/d (faithful-choice-literal)
                            (subcor-var len bx-mv-nths
                             faithful-choice-projections))))))

(local
 (defthm faithful-choice-axiom-of-bx
   (equal (bx-choose-axiom fn bound free body free2)
          (faithful-choice-axiom fn bound free body free2))
   :hints (("Goal"
            :in-theory (e/d (faithful-choice-axiom) (bx-choose-literal))))))

(local
 (defthm faithful-beta-reduce-of-bx
   (equal (faithful-beta-reduce expression bindings arguments-p)
          (if arguments-p
              (bx-beta-in-lst expression bindings)
            (bx-beta-in expression bindings)))
   :hints (("Goal" :induct (faithful-beta-reduce expression bindings arguments-p)
            :in-theory (disable assoc-equal pairlis$)))))

(local
 (defthm faithful-beta-normal-form-of-bx
   (equal (bx-beta term) (faithful-beta-normal-form term))
   :hints (("Goal" :in-theory (e/d (faithful-beta-normal-form)
                                   (faithful-beta-reduce bx-beta-in))))))

; The stored axiom supplies a nonempty list of bound variables when
; it supplies a choice statement at all.

(local
 (defthm faithful-choose-bound-one-is-list
   (true-listp (bx-bound-one formals actuals call))
   :rule-classes :type-prescription))

(local
 (defthm faithful-choose-bound-many-is-list
   (true-listp (bx-bound-many formals actuals mv i fuel))
   :rule-classes :type-prescription))

(local
 (defthm faithful-choice-bound-is-list
   (true-listp (car (bx-choose-parts axiom fn wrld)))
   :hints (("Goal"
            :in-theory (disable bx-bound-many bx-bound-one bx-bound-index
                                formals fgetprop)))
   :rule-classes :type-prescription))

(local
 (defthm faithful-no-choice-parts-without-axiom
   (equal (car (bx-choose-parts nil fn wrld)) nil)))

(local
 (defthm faithful-choice-data-of-items
   (implies (and (plist-worldp-with-formals wrld)
                 (equal (car line) "choose")
                 (member-equal (cons :stmt line) (bx-choose-items fn wrld)))
            (faithful-choice-data-p (cadr line) wrld))
   :hints (("Goal"
            :in-theory (e/d (faithful-choice-data-p)
                            (bx-choose-parts formals fgetprop bx-choose-axiom
                             bx-choose-literal
                             bx-beta plist-worldp-with-formals))
            :do-not-induct t))
   :rule-classes nil))

; A choice statement comes from a DEFCHOOSE outside a constraint.

(local
 (defthm faithful-choice-of-event
   (implies (and (equal (car line) "choose")
                 (plist-worldp-with-formals wrld)
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                          translations wrld))))
            (faithful-choice-data-p (cadr line) wrld))
   :hints (("Goal"
            :use (faithful-statement-word-of-event
                  (:instance faithful-choice-data-of-items
                             (fn (car (bx-names (bx-ev-namex ev))))))
            :in-theory (e/d (faithful-direct-event-result)
                            (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                                bx-names bx-programp bx-all-program-p
                                bx-some-program-p bx-constrained-p
                                bx-all-constrained-p bx-some-constrained-p
                                bx-program-defs bx-define-items bx-add-candidates
                                bx-stobj-items fgetprop bx-conjuncts
                                bx-mentions-some constraint-info bx-choose-items
                                bx-constrain-items bx-package-items
                                bx-formula-name bx-reserve-items
                                bx-names-with-content plist-worldp-with-formals bx-names-reserved))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-choice-of-origin
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and (equal (car line) "choose")
                   (plist-worldp-with-formals wrld)
                   origin)
              (faithful-choice-data-p (cadr line) wrld)))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  (:instance faithful-choice-of-event
                             (ev (car (faithful-statement-origin
                                       line lo hi translations wrld)))
                             (encl (cadr (faithful-statement-origin
                                         line lo hi translations wrld)))
                             (pending (caddr (faithful-statement-origin
                                             line lo hi translations wrld)))
                             (defined (cadddr (faithful-statement-origin
                                               line lo hi translations wrld)))))
            :in-theory (disable bx-event-items plist-worldp-with-formals)
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-choose-statement
  (implies
   (and (equal (car line) "choose")
        (plist-worldp-with-formals wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-choice-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-statement-has-origin
                 faithful-book-statement-has-origin
                 (:instance faithful-choice-of-origin (lo 0))
                 faithful-choice-of-origin)
           :in-theory (disable bx-library-lines bx-book-lines plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)
