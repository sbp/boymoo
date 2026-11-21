(in-package "ACL2")

(include-book "faithful-label-spelling")
(include-book "faithful-reserve")

; A generated label for a choice or defining equation identifies a
; sibling function. A position label identifies the constraint owner.

(defun faithful-conjunct-at-label-position (position current conjuncts)
  (declare (xargs :measure (acl2-count conjuncts)))
  (if (endp conjuncts)
      nil
    (if (equal position current)
        (car conjuncts)
      (faithful-conjunct-at-label-position position (+ 1 current) (cdr conjuncts)))))

(defund faithful-formula-of-label-in-constraint (label stored wrld)
  (let* ((anchor (faithful-label-anchor label))
         (key (faithful-label-key label))
         (formals (getprop anchor 'formals nil 'current-acl2-world wrld)))
    (case (car key)
      (:choice (getprop anchor 'defchoose-axiom nil 'current-acl2-world wrld))
      (:definition
       (if (unknown-constraints-p stored)
           (list 'equal (cons anchor formals)
                 (getprop anchor 'unnormalized-body nil 'current-acl2-world wrld))
         (faithful-first-defining-equation anchor formals stored)))
      (:constraint (faithful-conjunct-at-label-position (cadr key) 1 stored))
      (otherwise nil))))

(defund faithful-world-formula-for-generated-label (label wrld)
  (let* ((anchor (faithful-label-anchor label))
         (owner (faithful-constraint-owner anchor wrld)))
    (faithful-formula-of-label-in-constraint label (faithful-stored-constraint owner wrld)
                                           wrld)))

(local
 (defthm faithful-choice-label-anchor
   (implies (and (symbolp label)
                 (faithful-recorded-choice-p label axiom siblings wrld))
            (and (member-equal (faithful-label-anchor label) siblings)
                 (not (eql (faithful-symbol-last-character label) #\E))
                 (equal (car (faithful-label-key label)) :choice)
                 (equal (getprop (faithful-label-anchor label) 'defchoose-axiom nil
                                 'current-acl2-world wrld)
                        axiom)))
   :hints (("Goal"
            :induct (faithful-recorded-choice-p label axiom siblings wrld)
            :in-theory (e/d (faithful-recorded-choice-p) (fgetprop)))
           ("Subgoal *1/2"
            :use ((:instance faithful-generated-label-identifies-anchor
                             (fn (car siblings)) (kind :choice) (position 0)))
            :in-theory (enable faithful-label-purpose faithful-expected-label-key)))))

(local
 (defthm faithful-equation-label-anchor
   (implies (and (symbolp label)
                 (faithful-labeled-equation-p label term stored owner wrld))
            (and (member-equal (faithful-label-anchor label)
                               (faithful-constraint-siblings owner wrld))
                 (not (eql (faithful-symbol-last-character label) #\E))
                 (equal (faithful-formula-of-label-in-constraint label stored wrld) term)))
   :hints (("Goal"
            :use ((:instance faithful-generated-label-identifies-anchor
                             (fn (caadr term)) (kind :definition) (position 0)))
            :in-theory (e/d (faithful-labeled-equation-p faithful-label-purpose
                             faithful-expected-label-key faithful-formula-of-label-in-constraint)
                            (fgetprop unknown-constraints-p faithful-first-defining-equation))
            :do-not-induct t))))

(local
 (defthm faithful-conjunct-label-anchor
   (implies (and (symbolp label)
                 (natp position)
                 (faithful-indexed-conjunct-p label term conjuncts owner position))
            (and (equal (faithful-label-anchor label) owner)
                 (not (eql (faithful-symbol-last-character label) #\E))
                 (equal (car (faithful-label-key label)) :constraint)
                 (<= position (cadr (faithful-label-key label)))
                 (equal (faithful-conjunct-at-label-position
                         (cadr (faithful-label-key label)) position conjuncts)
                        term)))
   :hints (("Goal" :induct (faithful-indexed-conjunct-p label term conjuncts owner position))
           ("Subgoal *1/2"
            :use ((:instance faithful-generated-label-identifies-anchor
                             (fn owner) (kind :constraint) (label label)))
            :in-theory (enable faithful-label-purpose faithful-expected-label-key)))))

(local
 (defthm faithful-sibling-refers-to-owner
   (implies (and (faithful-constraint-members-p names owner wrld)
                 (member-equal name names))
            (and (equal (faithful-constraint-owner name wrld) owner)
                 (not (eq (getprop name 'formals t 'current-acl2-world wrld) t))))
   :hints (("Goal" :induct (faithful-constraint-members-p names owner wrld)
            :in-theory (disable fgetprop)))
   :rule-classes nil))

(local (include-book "std/lists/sets" :dir :system))

(local
 (defthm faithful-first-of-stripped-names
   (equal (car (strip-cars entries)) (caar entries))))

(local
 (defthm faithful-made-formula-anchor-is-in-group
   (let ((label (car pair)))
     (implies (and (faithful-constraint-formula-p pair stored owner wrld)
                   (faithful-unused-formula-name-p label wrld))
              (and (or (equal (faithful-label-anchor label) owner)
                       (member-equal (faithful-label-anchor label)
                                     (faithful-constraint-siblings owner wrld)))
                   (not (eql (faithful-symbol-last-character label) #\E))
                   (equal (faithful-formula-of-label-in-constraint label stored wrld)
                          (cadr pair)))))
   :hints (("Goal"
            :use ((:instance faithful-choice-label-anchor
                             (label (car pair)) (axiom (cadr pair))
                             (siblings (faithful-constraint-siblings owner wrld)))
                  (:instance faithful-equation-label-anchor
                             (label (car pair)) (term (cadr pair)))
                  (:instance faithful-conjunct-label-anchor
                             (label (car pair)) (term (cadr pair))
                             (conjuncts stored) (position 1)))
            :in-theory (e/d (faithful-constraint-formula-p faithful-formula-data-p
                             faithful-unused-formula-name-p faithful-name-in-use-p
                             faithful-formula-of-label-in-constraint)
                            (fgetprop faithful-indexed-conjunct-p unknown-constraints-p
                             faithful-conjunct-at-label-position faithful-first-defining-equation
                             faithful-choice-label-anchor faithful-equation-label-anchor
                             faithful-conjunct-label-anchor))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-formula-anchor-refers-to-owner
   (let* ((label (car pair))
          (owner (faithful-constraint-owner (caaar args) wrld))
          (anchor (faithful-label-anchor label)))
     (implies (and (faithful-constraint-data-p args wrld)
                   (faithful-constraint-formula-from-world-p pair args wrld)
                   (faithful-unused-formula-name-p label wrld))
              (and (equal (faithful-constraint-owner anchor wrld) owner)
                   (not (eql (faithful-symbol-last-character label) #\E))
                   (equal (faithful-world-formula-for-generated-label label wrld)
                          (cadr pair)))))
   :hints (("Goal"
            :use ((:instance faithful-made-formula-anchor-is-in-group
                             (owner (faithful-constraint-owner (caaar args) wrld))
                             (stored (faithful-stored-constraint
                                      (faithful-constraint-owner (caaar args) wrld)
                                      wrld)))
                  (:instance faithful-sibling-refers-to-owner
                             (name (faithful-label-anchor (car pair)))
                             (names (strip-cars (car args)))
                             (owner (faithful-constraint-owner (caaar args) wrld))))
            :in-theory (e/d (faithful-constraint-formula-from-world-p
                             faithful-constraint-data-p faithful-world-formula-for-generated-label)
                            (faithful-constraint-members-p unknown-constraints-p))
            :do-not-induct t))
   :rule-classes nil))

(defund faithful-line-constraint-owner (line wrld)
  (faithful-constraint-owner (caaar (cadr line)) wrld))

(defthm faithful-generated-constraint-label-identifies-world-formula
  (implies
   (and (equal (car line) "constrain")
        (member-equal pair (cadr (cadr line)))
        (faithful-unused-formula-name-p (car pair) wrld)
        (plist-worldp-with-formals wrld)
        (faithful-constraint-world-p wrld)
        (faithful-fact-world-p wrld)
        (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir cbd wrld)))))
   (and (equal (faithful-constraint-owner (faithful-label-anchor (car pair)) wrld)
               (faithful-line-constraint-owner line wrld))
        (equal (faithful-world-formula-for-generated-label (car pair) wrld)
               (cadr pair))
        (not (eql (faithful-symbol-last-character (car pair)) #\E))))
  :hints (("Goal"
           :use (faithful-constrain-statement faithful-constrain-formula-source
                 (:instance faithful-formula-anchor-refers-to-owner (args (cadr line))))
           :in-theory (e/d (faithful-line-constraint-owner)
                           (bx-library-lines bx-book-lines plist-worldp-with-formals))
           :do-not-induct t))
  :rule-classes nil)

; Sharing ties the lines to the same formula of the same constraint.

(defthm faithful-shared-generated-label-has-one-formula-and-owner
  (implies
   (and (equal (car first-line) "constrain")
        (equal (car second-line) "constrain")
        (member-equal first-pair (cadr (cadr first-line)))
        (member-equal second-pair (cadr (cadr second-line)))
        (equal (car first-pair) (car second-pair))
        (faithful-unused-formula-name-p (car first-pair) wrld)
        (plist-worldp-with-formals wrld)
        (faithful-constraint-world-p wrld)
        (faithful-fact-world-p wrld)
        (or (member-equal first-line
                          (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal first-line
                          (mv-nth 0 (bx-book-lines ground boot-hi lo hi translations
                                                   books-dir cbd wrld))))
        (or (member-equal second-line
                          (mv-nth 0 (bx-library-lines ground hi translations wrld)))
            (member-equal second-line
                          (mv-nth 0 (bx-book-lines ground boot-hi lo hi translations
                                                   books-dir cbd wrld)))))
   (and (equal (faithful-line-constraint-owner first-line wrld)
               (faithful-line-constraint-owner second-line wrld))
        (equal (cadr first-pair) (cadr second-pair))))
  :hints (("Goal"
           :use ((:instance faithful-generated-constraint-label-identifies-world-formula
                            (line first-line) (pair first-pair))
                 (:instance faithful-generated-constraint-label-identifies-world-formula
                            (line second-line) (pair second-pair)))
           :in-theory (disable bx-library-lines bx-book-lines plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)

; The name a line introduces is determined by its statement kind and
; arguments. A package introduces its imports rule as specified in
; spec/language.md, section 6.

(defund faithful-statement-introduces-name-p (name line)
  (let ((word (car line)) (args (cadr line)))
    (case-match word
      ("define" (member-equal name (strip-cars (cdr args))))
      ("constrain" (or (member-equal name (strip-cars (car args)))
                       (assoc-equal name (cadr args))))
      ("choose" (equal name (car args)))
      ("theorem" (equal name (car args)))
      ("axiom" (equal name (car args)))
      ("reserve" (equal name (car args)))
      ("package" (equal name (intern-in-package-of-symbol
                              (concatenate 'string (car args) "-PACKAGE") 'acl2::x)))
      (& nil))))

; The names of definition and choice events have their FORMALS record.
; Single-threaded object events test for that property before emitting
; a definition, so they need no analogous world condition.

(defun faithful-names-with-formals-p (names wrld)
  (if (endp names)
      t
    (and (not (eq (getprop (car names) 'formals t 'current-acl2-world wrld) t))
         (faithful-names-with-formals-p (cdr names) wrld))))

(defund faithful-function-event-record-p (event wrld)
  (or (not (member-equal (access-event-tuple-type event) '(defun defuns defchoose)))
      (faithful-names-with-formals-p (faithful-event-names event) wrld)))

(defun faithful-function-event-records-p (triples wrld)
  (if (endp triples)
      t
    (and (or (not (and (eq (caar triples) 'event-landmark)
                       (eq (cadar triples) 'global-value)))
             (faithful-function-event-record-p (cddar triples) wrld))
         (faithful-function-event-records-p (cdr triples) wrld))))

(defund faithful-function-event-world-p (wrld)
  (faithful-function-event-records-p wrld wrld))

(local
 (defthm faithful-function-event-record-of-landmark
   (implies (and (faithful-event-landmark-p event triples)
                 (faithful-function-event-records-p triples wrld))
            (faithful-function-event-record-p event wrld))
   :hints (("Goal" :induct (faithful-function-event-records-p triples wrld)
            :in-theory (enable faithful-event-landmark-p)))))

(local
 (defthm faithful-named-function-has-formals
   (implies (and (member-equal name names) (faithful-names-with-formals-p names wrld))
            (not (eq (getprop name 'formals t 'current-acl2-world wrld) t)))
   :hints (("Goal" :induct (faithful-names-with-formals-p names wrld)
            :in-theory (disable fgetprop)))
   :rule-classes nil))

(local
 (defthm faithful-name-of-bx-defs
   (implies (member-equal name (strip-cars (bx-defs fns wrld)))
            (member-equal name fns))
   :hints (("Goal" :in-theory (disable formals fgetprop)))))

(local
 (defthm faithful-name-of-bx-define-item
   (implies (and (equal (car line) "define")
                 (member-equal (cons :stmt line) (bx-define-items fns wrld))
                 (faithful-statement-introduces-name-p name line))
            (member-equal name fns))
   :hints (("Goal"
            :in-theory (e/d (faithful-statement-introduces-name-p)
                            (bx-defs bx-same-rulers bx-rulers))))))

(local
 (defthm faithful-name-of-bx-stobj-define-item
   (implies (and (equal (car line) "define")
                 (member-equal (cons :stmt line) (bx-stobj-define-items fns wrld))
                 (faithful-statement-introduces-name-p name line))
            (member-equal name fns))
   :hints (("Goal" :induct (bx-stobj-define-items fns wrld)
            :in-theory (disable bx-define-items))
           ("Subgoal *1/2"
            :use ((:instance faithful-name-of-bx-define-item (fns (list (car fns)))))))))

(local
 (defthm faithful-bx-ready-name
   (implies (member-equal name (bx-ready todo placed wrld))
            (member-equal name todo))
   :hints (("Goal" :in-theory (disable all-fnnames1 fgetprop)))))

(local
 (defthm faithful-name-of-bx-local-order
   (implies (and (not (stringp acc))
                 (member-equal name (bx-local-order todo placed acc wrld fuel)))
            (or (member-equal name todo)
                (member-equal name acc)))
   :hints (("Goal" :induct (bx-local-order todo placed acc wrld fuel)
            :in-theory (e/d (reverse) (bx-ready set-difference-equal))))))

(local
 (defthm faithful-stobj-definition-name-has-formals
   (implies (and (equal (car line) "define")
                 (not (stringp acc))
                 (not (stringp fns-acc))
                 (not (member-equal (cons :stmt line) acc))
                 (not (member-equal name fns-acc))
                 (faithful-statement-introduces-name-p name line)
                 (equal (getprop name 'formals t 'current-acl2-world wrld) t))
            (not (member-equal (cons :stmt line)
                               (bx-stobj-items names defined fns-acc wrld acc))))
   :hints (("Goal"
            :induct (bx-stobj-items names defined fns-acc wrld acc)
            :in-theory (e/d (reverse)
                            (bx-stobj-define-items bx-exec bx-local-order
                             bx-reserve-kind-p bx-programp hons-get formals fgetprop)))
           ("Subgoal *1/1"
            :use ((:instance faithful-name-of-bx-stobj-define-item
                             (fns (bx-local-order (reverse fns-acc) nil nil
                                                  wrld (len fns-acc))))
                  (:instance faithful-name-of-bx-local-order
                             (todo (reverse fns-acc)) (placed nil)
                             (acc nil) (fuel (len fns-acc))))))
   :rule-classes nil))

(local
 (defthm faithful-name-of-bx-choose-item
   (implies (and (equal (car line) "choose")
                 (member-equal (cons :stmt line) (bx-choose-items fn wrld))
                 (faithful-statement-introduces-name-p name line))
            (equal name fn))
   :hints (("Goal"
            :in-theory (e/d (faithful-statement-introduces-name-p)
                            (bx-choose-parts bx-choose-literal bx-choose-axiom
                             formals fgetprop bx-beta))))
   :rule-classes nil))

(local
 (defthm faithful-function-name-of-event-has-formals
   (implies (and (member-equal (car line) '("define" "choose"))
                 (faithful-function-event-record-p ev wrld)
                 name
                 (faithful-statement-introduces-name-p name line)
                 (member-equal (cons :stmt line)
                               (mv-nth 0 (faithful-direct-event ev encl pending defined
                                                               translations wrld))))
            (not (eq (getprop name 'formals t 'current-acl2-world wrld) t)))
   :hints (("Goal"
            :use (faithful-statement-word-of-event
                  (:instance faithful-event-type-reader (event ev))
                  (:instance faithful-event-name-reader (event ev))
                  (:instance faithful-named-function-has-formals
                             (names (faithful-event-names ev)))
                  (:instance faithful-name-of-bx-choose-item
                             (fn (car (faithful-event-names ev))))
                  (:instance faithful-stobj-definition-name-has-formals
                             (names (faithful-event-names ev)) (fns-acc nil) (acc nil)))
            :in-theory (e/d (faithful-direct-event-result faithful-function-event-record-p)
                            (bx-ev-type bx-ev-namex bx-ev-form bx-ev-symbol-class
                             access-event-tuple-type faithful-event-names bx-names
                             bx-programp bx-all-program-p bx-some-program-p bx-constrained-p
                             bx-all-constrained-p bx-some-constrained-p
                             bx-program-defs bx-define-items bx-add-candidates
                             bx-stobj-items fgetprop bx-conjuncts bx-mentions-some
                             constraint-info bx-choose-items bx-constrain-items bx-package-items
                             bx-reserve-items bx-names-with-content bx-names-reserved))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-function-name-of-origin-has-formals
   (let ((origin (faithful-statement-origin line lo hi translations wrld)))
     (implies (and origin
                   (member-equal (car line) '("define" "choose"))
                   (faithful-function-event-world-p wrld)
                   name
                   (faithful-statement-introduces-name-p name line))
              (not (eq (getprop name 'formals t 'current-acl2-world wrld) t))))
   :hints (("Goal"
            :use (faithful-statement-origin-produces-line
                  faithful-landmark-of-statement-origin
                  (:instance faithful-function-name-of-event-has-formals
                             (ev (car (faithful-statement-origin line lo hi translations wrld)))
                             (encl (cadr (faithful-statement-origin line lo hi translations wrld)))
                             (pending (caddr (faithful-statement-origin
                                              line lo hi translations wrld)))
                             (defined (cadddr (faithful-statement-origin
                                               line lo hi translations wrld)))))
            :in-theory (e/d (faithful-function-event-world-p)
                            (bx-event-items faithful-function-event-records-p fgetprop))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-function-introduction-has-formals
   (implies
    (and name
         (member-equal (car line) '("define" "choose"))
         (faithful-statement-introduces-name-p name line)
         (faithful-function-event-world-p wrld)
         (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
             (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                        translations books-dir cbd wrld)))))
    (not (eq (getprop name 'formals t 'current-acl2-world wrld) t)))
   :hints (("Goal"
            :use (faithful-library-statement-has-origin faithful-book-statement-has-origin
                  (:instance faithful-function-name-of-origin-has-formals (lo 0))
                  faithful-function-name-of-origin-has-formals)
            :in-theory (disable bx-library-lines bx-book-lines fgetprop)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-constrained-function-introduction-has-formals
   (implies (and (faithful-constraint-data-p args wrld)
                 (member-equal name (strip-cars (car args))))
            (not (eq (getprop name 'formals t 'current-acl2-world wrld) t)))
   :hints (("Goal"
            :use ((:instance faithful-sibling-refers-to-owner
                             (names (strip-cars (car args)))
                             (owner (faithful-constraint-owner (caaar args) wrld))))
            :in-theory (e/d (faithful-constraint-data-p)
                            (faithful-constraint-members-p fgetprop))
            :do-not-induct t))
   :rule-classes nil))

; An ordinary declaration uses a world name or a package rule. A
; symbol unused in the world with the ending of a generated label can
; only be introduced as a constraint formula label.

(local
 (defthm faithful-unused-generated-name-can-only-label-formula
   (implies
    (and (faithful-statement-introduces-name-p name line)
         (faithful-unused-formula-name-p name wrld)
         (not (equal (faithful-symbol-last-character name) #\E))
         (plist-worldp-with-formals wrld)
         (faithful-constraint-world-p wrld)
         (faithful-fact-world-p wrld)
         (faithful-function-event-world-p wrld)
         (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
             (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                        translations books-dir cbd wrld)))))
    (and (equal (car line) "constrain")
         (assoc-equal name (cadr (cadr line)))))
   :hints (("Goal"
            :use (faithful-function-introduction-has-formals
                  faithful-fact-statement-has-world-record
                  faithful-reserve-statement faithful-constrain-statement
                  (:instance faithful-constrained-function-introduction-has-formals
                             (args (cadr line))))
            :in-theory (e/d (faithful-statement-introduces-name-p
                             faithful-unused-formula-name-p faithful-name-in-use-p
                             faithful-reserve-data-p)
                            (bx-book-lines bx-library-lines fgetprop assoc-equal
                             plist-worldp-with-formals string-append))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm faithful-assoc-selects-named-pair
   (implies (assoc-equal name pairs)
            (and (member-equal (assoc-equal name pairs) pairs)
                 (equal (car (assoc-equal name pairs)) name)))
   :hints (("Goal" :induct (assoc-equal name pairs)))))

(defthm faithful-generated-name-introductions-stay-with-owner
  (let ((name (car pair)))
    (implies
     (and (equal (car constraint) "constrain")
          (member-equal pair (cadr (cadr constraint)))
          (faithful-unused-formula-name-p name wrld)
          (faithful-statement-introduces-name-p name line)
          (plist-worldp-with-formals wrld)
          (faithful-constraint-world-p wrld)
          (faithful-fact-world-p wrld)
          (faithful-function-event-world-p wrld)
          (or (member-equal constraint
                            (mv-nth 0 (bx-library-lines ground hi translations wrld)))
              (member-equal constraint
                            (mv-nth 0 (bx-book-lines ground boot-hi lo hi translations
                                                     books-dir cbd wrld))))
          (or (member-equal line (mv-nth 0 (bx-library-lines ground hi translations wrld)))
              (member-equal line (mv-nth 0 (bx-book-lines ground boot-hi lo hi
                                                         translations books-dir cbd wrld)))))
     (and (equal (car line) "constrain")
          (assoc-equal name (cadr (cadr line)))
          (equal (cadr (assoc-equal name (cadr (cadr line)))) (cadr pair))
          (equal (faithful-line-constraint-owner constraint wrld)
                 (faithful-line-constraint-owner line wrld)))))
  :hints (("Goal"
           :use ((:instance faithful-generated-constraint-label-identifies-world-formula
                            (line constraint))
                 (:instance faithful-unused-generated-name-can-only-label-formula
                            (name (car pair)))
                 (:instance faithful-shared-generated-label-has-one-formula-and-owner
                            (first-line constraint) (first-pair pair)
                            (second-line line)
                            (second-pair (assoc-equal (car pair) (cadr (cadr line))))))
           :in-theory (disable bx-library-lines bx-book-lines assoc-equal
                               plist-worldp-with-formals)
           :do-not-induct t))
  :rule-classes nil)
