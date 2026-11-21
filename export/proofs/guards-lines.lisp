(in-package "ACL2")

(include-book "guards-report")
(local (include-book "system/pseudo-termp-lemmas" :dir :system))
(local (include-book "tools/flag" :dir :system))

(local
 (in-theory (disable fgetprop formals plist-worldp bx-world-properties-p
                     bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                     bx-event-tuple-p bx-event-fields-p bx-event-names-p
                     bx-definitions-p bx-arity-list-p bx-named-formulas-p
                     bx-line-p pseudo-termp pseudo-term-listp bx-introduced bx-used
                     hons-get bx-package-rule bx-defun-forms)))

; A program line introduced by an event is a definition line. Filtering
; lists of lines retains the shape of their members.

(verify-guards bx-words
  :hints (("Goal" :in-theory (disable bx-item-listp-implies-alistp
                                     bx-line-listp-implies-alistp
                                     bx-known-package-alist-is-alist
                                     bx-alistp-when-definition-forms-p
                                     bx-definition-list-structure
                                     bx-arities-list-structure
                                     bx-named-formula-list-structure))))
(verify-guards bx-not-ground
  :hints (("Goal" :in-theory (enable bx-line-p))))

(local
 (defthm bx-line-args-are-true-list
   (implies (bx-line-p line)
            (true-listp (cadr line)))
   :hints (("Goal" :expand ((bx-line-p line))
            :in-theory (disable bx-line-p-implies-cons)))))

(local
 (defthm bx-line-cons-fields
   (implies (bx-line-p line)
            (and (iff (consp (cdr line)) (cdr line))
                 (iff (consp (cadr line)) (cadr line))
                 (iff (consp (cdadr line)) (cdadr line))
                 (iff (consp (cddadr line)) (cddadr line))
                 (iff (consp (cdddr (cadr line))) (cdddr (cadr line)))))
   :hints (("Goal" :use (bx-line-args-are-true-list
                         (:instance bx-line-p-implies-cons (x line)))
            :in-theory (disable bx-line-args-are-true-list bx-line-p-implies-cons)))))

(local
 (defthm bx-definitions-in-define-line
   (implies (and (bx-line-p line) (equal (car line) "define"))
            (bx-definitions-p (cdr (cadr line))))
   :hints (("Goal" :expand ((bx-line-p line))
            :in-theory (disable bx-line-p-implies-cons)))))

(verify-guards bx-program-only
  :hints (("Goal"
           :use ((:instance bx-definitions-in-define-line (line (car progs)))
                 (:instance bx-definition-list-structure (defs (cdadar progs)))
                 (:instance bx-line-cons-fields (line (car progs))))
           :expand ((bx-definition-lines-p progs))
           :in-theory (disable bx-line-p strip-cars bx-definitions-in-define-line
                               bx-definition-list-structure bx-line-cons-fields)
           :do-not-induct t)))
(verify-guards bx-library-program-order)
(verify-guards bx-runnable)

(local
 (defthm bx-line-list-p-of-append
   (implies (and (bx-line-list-p x) (bx-line-list-p y))
            (bx-line-list-p (append x y)))))

(local
 (defthm bx-line-list-p-of-revappend
   (implies (and (bx-line-list-p x) (bx-line-list-p y))
            (bx-line-list-p (revappend x y)))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defthm bx-line-list-p-of-words
   (implies (bx-line-list-p x)
            (bx-line-list-p (bx-words words x)))))

(local
 (defthm bx-program-only-preserves-definitions
   (implies (bx-definition-lines-p progs)
            (bx-definition-lines-p (bx-program-only progs wrld)))
   :hints (("Goal" :induct (bx-program-only progs wrld)
            :in-theory (disable bx-all-program-p strip-cars)))))

(defthm bx-library-program-order-returns-lines
  (implies (and (bx-definition-lines-p progs) (bx-line-list-p ordered))
           (bx-line-list-p (bx-library-program-order progs ordered wrld)))
  :hints (("Goal" :in-theory (disable bx-words bx-program-only))))

(defthm bx-not-ground-preserves-lines
  (and (implies (bx-line-list-p x)
                (bx-line-list-p (bx-not-ground x ground)))
       (implies (bx-definition-lines-p x)
                (bx-definition-lines-p (bx-not-ground x ground))))
  :hints (("Goal" :induct (bx-not-ground x ground)
           :in-theory (disable bx-line-p))))

; The library walk holds lines in its index and in every stack frame.

(verify-guards bx-index-fns)
(verify-guards bx-line-index-p)
(verify-guards bx-index)
(verify-guards bx-steps)
(verify-guards bx-walk-stack-p)

(local
 (defthm bx-line-index-p-of-index-fns
   (implies (and (bx-line-p stmt) (bx-line-index-p index))
            (bx-line-index-p (bx-index-fns fns stmt index)))))

(local
 (defthm bx-line-index-p-of-index
   (implies (and (bx-line-list-p x) (bx-line-index-p index))
            (bx-line-index-p (bx-index x index)))
   :hints (("Goal" :in-theory (disable bx-index-fns bx-line-p)))))

(local
 (defthm bx-index-lookup-returns-line
   (implies (and (bx-line-index-p index) (cdr (hons-get key index)))
            (bx-line-p (cdr (hons-get key index))))
   :hints (("Goal" :in-theory (enable hons-get)))))

(local
 (defthm bx-naturalp-of-steps
   (natp (bx-steps stmts))
   :rule-classes :type-prescription))

(verify-guards bx-walk
  :hints (("Goal" :in-theory (disable bx-line-p bx-note))))

(local
 (defthm bx-walk-shape
   (implies (and (bx-walk-stack-p stack) (bx-line-list-p todo)
                 (bx-line-index-p index) (bx-line-list-p acc) (bx-item-list-p notes))
            (and (bx-line-list-p (car (bx-walk stack todo index done acc notes fuel)))
                 (bx-item-list-p (mv-nth 1 (bx-walk stack todo index done acc notes fuel)))))
   :hints (("Goal" :induct (bx-walk stack todo index done acc notes fuel)
            :in-theory (disable bx-line-p)))))

(local
 (defthm bx-walk-lines-are-true-list
   (implies (true-listp acc)
            (true-listp (car (bx-walk stack todo index done acc notes fuel))))
   :hints (("Goal" :induct (bx-walk stack todo index done acc notes fuel)
            :in-theory (disable bx-walk-shape bx-line-listp-implies-alistp
                                bx-line-p-implies-cons bx-note)))))

(local
 (defthm bx-walk-notes-are-true-list
   (implies (true-listp notes)
            (true-listp (mv-nth 1 (bx-walk stack todo index done acc notes fuel))))
   :hints (("Goal" :induct (bx-walk stack todo index done acc notes fuel)
            :in-theory (disable bx-walk-shape bx-line-listp-implies-alistp
                                bx-line-p-implies-cons)))))

(verify-guards bx-library-order
  :hints (("Goal" :in-theory (disable bx-walk bx-index bx-steps bx-words)
           :do-not-induct t)))

(defthm bx-library-order-shape
  (implies (bx-line-list-p stmts)
           (and (bx-line-list-p (car (bx-library-order stmts)))
                (bx-item-list-p (mv-nth 1 (bx-library-order stmts)))))
  :hints (("Goal" :in-theory (disable bx-walk bx-index bx-steps bx-words))))

(defthm bx-library-order-notes-are-true-list
  (true-listp (mv-nth 1 (bx-library-order stmts)))
  :hints (("Goal" :in-theory (disable bx-walk bx-index bx-steps bx-words))))

; Checking a statement walks its terms and looks up names and arities
; in the tables. The function names collected by the walk are symbols.

(local
 (defthm bx-bad-call-names-of-append
   (implies (and (symbol-listp x) (symbol-listp y))
            (symbol-listp (append x y)))
   :hints (("Goal" :induct (append x y)))))

(local (make-flag bx-bad-calls-flag bx-bad-calls))

(defthm-bx-bad-calls-flag
  (defthm bx-symbol-listp-of-bad-calls
    (implies (pseudo-termp term)
             (symbol-listp (bx-bad-calls term fns own)))
    :flag bx-bad-calls)
  (defthm bx-symbol-listp-of-bad-calls-lst
    (implies (pseudo-term-listp terms)
             (symbol-listp (bx-bad-calls-lst terms fns own)))
    :flag bx-bad-calls-lst)
  :hints (("Goal" :in-theory (enable pseudo-termp pseudo-term-listp))))

(local
 (defthm bx-packages-of-preserves-list
   (implies (true-listp acc)
            (true-listp (bx-packages-of x pkgs acc)))
   :hints (("Goal" :induct (bx-packages-of x pkgs acc)))))

(local
 (defthm bx-imported-names-preserves-symbol-list
   (implies (symbol-listp acc)
            (symbol-listp (bx-imported-names x pkgs acc)))
   :hints (("Goal" :induct (bx-imported-names x pkgs acc)))))

(verify-guards bx-packages-of)
(verify-guards bx-imported-names)
(verify-guards bx-add-imports)
(verify-guards bx-new-names)
(verify-guards bx-add-arities)
(verify-guards bx-def-arities)
(verify-guards bx-alist)
(verify-guards bx-package-rule)

(local
 (defthm bx-arity-list-p-of-def-arities
   (implies (bx-definitions-p defs)
            (bx-arity-list-p (bx-def-arities defs)))
   :hints (("Goal" :in-theory (enable bx-definitions-p bx-arity-list-p)))))

(local
 (defthm bx-alistp-of-bx-alist
   (alistp (bx-alist pairs))))

(local
 (defthm bx-fields-of-package-line
   (implies (and (bx-line-p stmt)
                 (member-equal (car stmt) '("package" "hidden-package")))
            (and (stringp (caadr stmt))
                 (symbol-listp (cadadr stmt))))
   :hints (("Goal" :expand ((bx-line-p stmt))
            :in-theory (disable bx-line-p-implies-cons)))))

(local
 (defthm bx-fields-of-constraint-line
   (implies (and (bx-line-p stmt) (equal (car stmt) "constrain"))
            (and (bx-arity-list-p (caadr stmt))
                 (bx-named-formulas-p (cadadr stmt))))
   :hints (("Goal" :expand ((bx-line-p stmt))
            :in-theory (disable bx-line-p-implies-cons)))))

(local
 (defthm bx-body-of-choice-line
   (implies (and (bx-line-p stmt) (equal (car stmt) "choose"))
            (pseudo-termp (cadddr (cadr stmt))))
   :hints (("Goal" :expand ((bx-line-p stmt))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '((:executable-counterpart equal)))))))

(local
 (defthm bx-formula-of-fact-line
   (implies (and (bx-line-p stmt) (member-equal (car stmt) '("theorem" "axiom")))
            (pseudo-termp (cadadr stmt)))
   :hints (("Goal" :expand ((bx-line-p stmt))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(member-equal (:executable-counterpart equal)))))))

(local
 (defthm bx-pseudo-term-listp-of-singleton
   (equal (pseudo-term-listp (list x)) (pseudo-termp x))
   :hints (("Goal" :in-theory (enable pseudo-term-listp)))))

(verify-guards bx-check-stmt
  :hints (("Goal"
           :in-theory (disable bx-def-arities bx-alist bx-bodies bx-bad-calls-lst
                               bx-packages-of bx-imported-names bx-add-arities
                               bx-add-names bx-add-imports bx-new-names
                               bx-pseudo-term-list-components strip-cars strip-cadrs)
           :do-not-induct t)))

; The seen table binds each statement key to a proper list.

(local
 (defthm bx-first-definition-is-cons-or-nil
   (implies (bx-definitions-p defs)
            (iff (consp (car defs)) (car defs)))
   :hints (("Goal" :expand ((bx-definitions-p defs))))))

(local
 (defthm bx-arity-records-are-cons-or-nil
   (implies (bx-arity-list-p pairs)
            (and (iff (consp pairs) pairs)
                 (iff (consp (car pairs)) (car pairs))))
   :hints (("Goal" :expand ((bx-arity-list-p pairs))))))

(verify-guards bx-stmt-key
  :hints (("Goal" :do-not-induct t)))
(verify-guards bx-seen-lines-p)

(local
 (defthm bx-list-of-seen-lookup
   (implies (bx-seen-lines-p seen)
            (true-listp (cdr (hons-get key seen))))
   :hints (("Goal" :in-theory (enable hons-get)))))

(verify-guards bx-check-stmts
  :hints (("Goal" :use ((:instance bx-line-cons-fields (line (car stmts))))
           :expand ((bx-line-list-p stmts))
           :in-theory (disable bx-check-stmt bx-stmt-key bx-line-cons-fields)
           :do-not-induct t)))

(local
 (defthm bx-item-lists-preserved-by-revappend
   (implies (and (bx-item-list-p x) (bx-item-list-p y))
            (bx-item-list-p (revappend x y)))
   :hints (("Goal" :induct (revappend x y)))))

(defthm bx-check-stmts-shape
  (implies (and (bx-seen-lines-p seen) (bx-item-list-p notes))
           (and (bx-item-list-p (car (bx-check-stmts stmts fns names pkgs seen notes)))
                (bx-seen-lines-p
                 (mv-nth 4 (bx-check-stmts stmts fns names pkgs seen notes)))))
  :hints (("Goal" :induct (bx-check-stmts stmts fns names pkgs seen notes)
           :in-theory (disable bx-check-stmt bx-stmt-key bx-line-p))))

(defthm bx-check-stmts-notes-are-true-list
  (implies (true-listp notes)
           (true-listp (car (bx-check-stmts stmts fns names pkgs seen notes))))
  :hints (("Goal" :induct (bx-check-stmts stmts fns names pkgs seen notes)
           :in-theory (disable bx-check-stmt bx-stmt-key bx-check-stmts-shape))))

; The ground tables start with the primitives and declared ground functions.

(verify-guards bx-add-package-imports)
(verify-guards bx-ground-tables
  :hints (("Goal" :in-theory (disable bx-arities bx-add-arities bx-add-names
                                     bx-add-package-imports bx-functions-present-p
                                     binary-append)
           :do-not-induct t)))
