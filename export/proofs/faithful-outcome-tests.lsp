(in-package "ACL2")

; The extra formula for a nullary strengthened choice includes a
; reflexive equality. ACL2 stores it even though the second list of free
; variables is empty.

(defun faithful-test-strengthened-nullary-axiom-p (args wrld)
  (let* ((fn (car args))
         (bound (cadr args))
         (body (cadddr args))
         (stored (faithful-beta-normal-form
                  (getprop fn 'defchoose-axiom nil 'current-acl2-world wrld))))
    (and (equal stored
                (faithful-beta-normal-form
                 (faithful-choice-literal fn bound nil body nil t)))
         (not (equal stored
                     (faithful-beta-normal-form
                      (faithful-choice-axiom fn bound nil body nil)))))))

(assign faithful-choice-lo (max-absolute-event-number (w state)))

(defchoose faithful-closed-choice x ()
  (equal x 'sample)
  :strengthen t)

(defchoose faithful-closed-pair (x y) ()
  (equal (cons x y) '(sample . datum))
  :strengthen t)

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-choice-lo)
                 (max-absolute-event-number (w state)) nil "" "" (w state))
  (declare (ignore program aids))
  (let ((expected
         '(("choose" (faithful-closed-choice (x) nil (equal x 'sample) nil))
           ("choose" (faithful-closed-pair (x y) nil
                      (equal (cons x y) '(sample . datum)) nil)))))
    (faithful-test "strengthened nullary choice"
                   (and (equal statements expected)
                        (not (faithful-first-statement-problem statements (w state)))
                        (faithful-test-strengthened-nullary-axiom-p
                         (cadr (car statements)) (w state))
                        (faithful-test-strengthened-nullary-axiom-p
                         (cadr (cadr statements)) (w state))
                        (not (member-equal
                              '("note" ("defchoose axiom not of the form of spec/logic.md"
                                        faithful-closed-choice))
                              notes))
                        (not (member-equal
                              '("note" ("defchoose axiom not of the form of spec/logic.md"
                                        faithful-closed-pair))
                              notes))))))

; The signed encapsulate's range contains the exhausted constraint.
; Its note names the function, the law and the conjunct with an
; available generated label.

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-label-lo)
                 (@ faithful-label-hi) nil "" "" (w state))
  (declare (ignore program aids))
  (let* ((name '|FAITHFUL-COLLISION constraint 1 1000|)
         (stored-fact (getprop name 'theorem nil 'current-acl2-world (w state))))
    (faithful-test "constraint label exhaustion"
                   (and stored-fact
                        (member-equal (list "theorem" (list name stored-fact)) statements)
                        (not (member-equal "constrain" (strip-cars statements)))
                        (member-equal
                         '("note" ("constraint with a formula for which no unused name was found"
                                   (faithful-collision faithful-collision-law
                                    |FAITHFUL-COLLISION constraint 2|)))
                         notes)))))

(defun faithful-test-function-in-constraint-p (fn statements)
  (if (endp statements)
      nil
    (let ((line (car statements)))
      (or (and (equal (car line) "constrain")
               (assoc-eq fn (car (cadr line))))
          (faithful-test-function-in-constraint-p fn (cdr statements))))))

(mv-let (statements program notes)
  (bx-library-lines (@ faithful-ground-fns) (@ faithful-label-hi)
                    nil (w state))
  (declare (ignore program))
  (faithful-test "library constraint label exhaustion"
                 (and (not (faithful-test-function-in-constraint-p
                            'faithful-collision statements))
                      (faithful-constraint-report-present-p
                       :missing-label 'faithful-collision notes (w state))
                      (member-equal
                       '("note" ("constraint with a formula for which no unused name was found"
                                 (faithful-collision faithful-collision-law
                                  |FAITHFUL-COLLISION constraint 2|)))
                       notes))))

; A package imports the keyword whose spelling would be the first
; conjunct label. Two independent definitions follow the constraint
; because the first calls its function and the second calls the first.

(defun faithful-note-of-kind-p (key notes)
  (if (endp notes)
      nil
    (or (equal key (caadar notes))
        (faithful-note-of-kind-p key (cdr notes)))))

(assign faithful-routing-lo (max-absolute-event-number (w state)))

(defpkg "FAITHFUL-ROUTING" '(:|F constraint 1|))

(encapsulate
  (((faithful-routing::f *) => *))
  (local (defun faithful-routing::f (x) x))
  (defun faithful-route-one (x) (faithful-routing::f x))
  (defun faithful-route-two (x) (faithful-route-one x))
  (defthm faithful-routing-law
    (equal (faithful-routing::f x) x)
    :rule-classes
    ((:rewrite :corollary
               (equal (faithful-routing::f (cons x y)) (cons x y))))))

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-routing-lo)
                 (max-absolute-event-number (w state)) nil "" "" (w state))
  (declare (ignore program aids))
  (faithful-test "constraint labels and deferred definitions"
                 (and (equal (strip-cars statements)
                             '("package" "constrain" "define" "define"))
                      (member-equal
                       '("constrain"
                         (((faithful-routing::f 1))
                          ((faithful-routing-law (equal (faithful-routing::f x) x))
                           (faithful-routing::|F constraint 1 1|
                            (equal (faithful-routing::f (cons x y)) (cons x y))))))
                       statements)
                      (equal (cadr (cadr (nth 2 statements)))
                             '(faithful-route-one (x) (faithful-routing::f x)))
                      (equal (cadr (cadr (nth 3 statements)))
                             '(faithful-route-two (x) (faithful-route-one x)))
                      (not (faithful-note-of-kind-p
                            "line that could not be admitted in order" notes))
                      (not (faithful-first-statement-problem statements (w state))))))

; A sibling whose defining equation belongs to the constraint stays in
; the group. A definition independent of the signature remains outside.

(assign faithful-mixed-lo (max-absolute-event-number (w state)))

(encapsulate
  (((faithful-mixed-f *) => *))
  (local (defun faithful-mixed-f (x) x))
  (defun faithful-mixed-independent (x) (cons x x))
  (defun faithful-mixed-sibling (x) (faithful-mixed-f x))
  (defthm faithful-mixed-law
    (equal (faithful-mixed-sibling (faithful-mixed-independent x))
           (faithful-mixed-independent x))
    :rule-classes nil))

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-mixed-lo)
                 (max-absolute-event-number (w state)) nil "" "" (w state))
  (declare (ignore program aids))
  (let* ((args (cadr (cadr statements)))
         (equation (assoc-equal '|FAITHFUL-MIXED-SIBLING definition| (cadr args))))
    (faithful-test "definition equation of a constraint sibling"
                   (and (equal (strip-cars statements) '("define" "constrain"))
                        (equal (cadr (cadar statements))
                               '(faithful-mixed-independent (x) (cons x x)))
                        (equal (car args)
                               '((faithful-mixed-f 1) (faithful-mixed-sibling 1)))
                        (equal equation
                               '(|FAITHFUL-MIXED-SIBLING definition|
                                 (equal (faithful-mixed-sibling x) (faithful-mixed-f x))))
                        (not (faithful-note-of-kind-p
                              "line that could not be admitted in order" notes))
                        (not (faithful-first-statement-problem statements (w state)))))))

; The event landmarks below put two constrained functions inside an
; encapsulate whose recorded sibling list names only the signature.

(let* ((lo (max-absolute-event-number (w state)))
       (hi (+ 3 lo))
       (wrld
        (list*
         (list 'event-landmark 'global-value hi
               '((encapsulate) (faithful-only-sibling) . :ideal)
               'encapsulate '(((faithful-only-sibling) => *)))
         (list 'event-landmark 'global-value (cons (+ 2 lo) 1)
               (cons '(defchoose) (cons 'faithful-unlisted-choice :ideal))
               'defchoose 'faithful-unlisted-choice 'x nil '(equal x 'sample))
         (list 'event-landmark 'global-value (cons (+ 1 lo) 1)
               (cons '(defun) (cons 'faithful-unlisted-definition :ideal))
               'defun 'faithful-unlisted-definition nil ''sample)
         '(faithful-only-sibling constraint-lst-etc nil)
         '(faithful-only-sibling siblings faithful-only-sibling)
         '(faithful-only-sibling formals)
         '(faithful-unlisted-definition constraint-lst-etc faithful-only-sibling)
         '(faithful-unlisted-choice constraint-lst-etc faithful-only-sibling)
         '(faithful-unlisted-choice defchoose-axiom equal (faithful-unlisted-choice) 'sample)
         (w state))))
  (mv-let (statements program notes aids)
    (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) lo hi nil "" "" wrld)
    (declare (ignore program aids))
    (faithful-test "unlisted constrained functions"
                   (and (equal statements '(("constrain" (((faithful-only-sibling 0)) nil))))
                        (not (faithful-first-statement-problem statements wrld))
                        (member-equal
                         '("note" ("constrained definition of functions that its constraint does not list"
                                   (faithful-unlisted-definition)))
                         notes)
                        (member-equal
                         '("note" ("constrained choice of a function that its constraint does not list"
                                   faithful-unlisted-choice))
                         notes)))))

; FACT0 is an axiom of the sampled books with no name in the ground theory.

(mv-let (statements program notes)
  (bx-library-lines (@ faithful-ground-fns) (@ faithful-sample-hi) nil (w state))
  (declare (ignore program notes))
  (let ((formula (getprop 'fact0 'theorem nil 'current-acl2-world (w state))))
    (faithful-test "library axiom outside the ground theory"
                   (and formula
                        (member-equal (list "axiom" (list 'fact0 formula)) statements)))))

; A constraint label belongs to its anchor's own package. Each of
; these packages imports a symbol whose spelling would be the base label.

(assign faithful-shared-label-lo (max-absolute-event-number (w state)))

(defpkg "FAITHFUL-LABEL-A" '(acl2::|F constraint 1|))
(defpkg "FAITHFUL-LABEL-B" '(acl2::|F constraint 1|))

(encapsulate
  (((faithful-label-a::f *) => *))
  (local (defun faithful-label-a::f (x) x))
  (defthm faithful-label-a-law
    (equal (faithful-label-a::f x) x)
    :rule-classes
    ((:rewrite :corollary
               (equal (faithful-label-a::f (cons x y)) (cons x y))))))

(encapsulate
  (((faithful-label-b::f *) => *))
  (local (defun faithful-label-b::f (x) x))
  (defthm faithful-label-b-law
    (equal (faithful-label-b::f x) x)
    :rule-classes
    ((:rewrite :corollary
               (equal (faithful-label-b::f (cons x y)) (cons x y))))))

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-shared-label-lo)
                 (max-absolute-event-number (w state)) nil "" "" (w state))
  (declare (ignore program aids))
  (let* ((first (nth 2 statements))
         (second (nth 3 statements))
         (first-label 'faithful-label-a::|F constraint 1 1|)
         (second-label 'faithful-label-b::|F constraint 1 1|)
         (first-pair (assoc-equal first-label (cadr (cadr first))))
         (second-pair (assoc-equal second-label (cadr (cadr second)))))
    (faithful-test "imported constraint label passed over"
                   (and (equal (strip-cars statements)
                               '("package" "package" "constrain" "constrain"))
                        (faithful-unused-formula-name-p 'acl2::|F constraint 1| (w state))
                        (eq (faithful-label-anchor first-label) 'faithful-label-a::f)
                        (eq (faithful-label-anchor second-label) 'faithful-label-b::f)
                        (equal (faithful-label-key first-label) '(:constraint 1))
                        (equal (faithful-label-key second-label) '(:constraint 1))
                        (equal first-pair
                               (list first-label
                                     '(equal (faithful-label-a::f (cons x y)) (cons x y))))
                        (equal second-pair
                               (list second-label
                                     '(equal (faithful-label-b::f (cons x y)) (cons x y))))
                        (not (faithful-first-statement-problem statements (w state)))
                        (not (faithful-note-of-kind-p
                              "line that could not be admitted in order" notes))))))
