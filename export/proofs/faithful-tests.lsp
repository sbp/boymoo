(in-package "ACL2")

; Save each world before admitting the proof and test functions.

(assign faithful-boot-world (w state))
(assign faithful-boot-hi (max-absolute-event-number (w state)))

(include-book "misc/hidden-defpkg-checks/top" :dir :system
              :uncertified-okp nil :skip-proofs-okp nil :ttags nil)
(assign faithful-hidden-world (w state))

(include-book "misc/defpun" :dir :system
              :uncertified-okp nil :skip-proofs-okp nil :ttags nil)
(assign faithful-defpun-world (w state))

(include-book "std/alists/alist-equiv" :dir :system
              :uncertified-okp nil :skip-proofs-okp nil :ttags nil)
(assign faithful-alist-equiv-world (w state))

(include-book "std/stobjs/absstobjs" :dir :system
              :uncertified-okp nil :skip-proofs-okp nil :ttags nil)
(assign faithful-absstobjs-world (w state))

; This sample supplies axioms to the exporter. The proof books certify
; in separate ACL2 sessions with axioms disallowed.

(include-book "misc/dft-ex" :dir :system :defaxioms-okp t
              :uncertified-okp nil :skip-proofs-okp nil :ttags nil)
(assign faithful-dft-world (w state))

(include-book "misc/defattach-example" :dir :system
              :uncertified-okp nil :skip-proofs-okp nil :ttags nil)

(defpkg "FAITHFUL-EXAMPLE" '(acl2::faithful-package-symbol))

(ld "export/choice.lisp" :ld-error-action :error)

(encapsulate
  (((faithful-guarded *) => *))
  (local (defun faithful-guarded (x) x))
  (defthm faithful-guarded-law
    (and (equal (ec-call (faithful-guarded x)) x)
         (equal (faithful-guarded (cons x y)) (cons x y)))
    :rule-classes nil))

(defun faithful-executable-example (x)
  (declare (xargs :mode :program))
  (mbe :logic x :exec (cons x x)))

(assign faithful-sample-world (w state))
(assign faithful-sample-hi (max-absolute-event-number (w state)))

; Occupy every spelling that the exporter can try for the first
; unnamed conjunct. The final spelling names a different theorem.

(defun faithful-occupy-conjunct-labels (index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (let* ((base "FAITHFUL-COLLISION constraint 1")
           (spelling (if (zp index)
                         base
                       (concatenate 'string base " "
                                    (coerce (explode-nonnegative-integer index 10 nil)
                                            'string))))
           (name (intern-in-package-of-symbol spelling 'faithful-collision)))
      (cons (list 'deflabel name)
            (faithful-occupy-conjunct-labels (+ 1 (nfix index)) (- count 1))))))

(assign faithful-label-lo (max-absolute-event-number (w state)))

(with-output :off :all
  (make-event (cons 'progn (faithful-occupy-conjunct-labels 0 1000))))

(defthm |FAITHFUL-COLLISION constraint 1 1000|
  (equal (cons x y) (cons x y))
  :rule-classes nil)

(encapsulate
  (((faithful-collision *) => *))
  (local (defun faithful-collision (x) x))
  (defthm faithful-collision-law
    (equal (faithful-collision x) x)
    :rule-classes
    ((:rewrite :corollary
               (equal (faithful-collision (cons x y)) (cons x y)))
     (:rewrite :corollary
               (equal (faithful-collision (list x)) (list x))))))

(assign faithful-label-hi (max-absolute-event-number (w state)))

(include-book "build/export/acl2/faithful-attachments"
              :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil
              :ttags nil)
(include-book "build/export/acl2/faithful-constraint-outcomes"
              :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil
              :ttags nil)
(include-book "build/export/acl2/faithful-generated-names"
              :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil
              :ttags nil)
(set-guard-checking :none)

; Every test writes a single result. A failed world test also gives the
; values of the hypotheses, in the order listed here.

(defmacro faithful-test (name form)
  (list 'if form
        (list 'cw "~%faithful-test: ~s0 ok~%" name)
        (list 'cw "~%faithful-test: ~s0 failed~%" name)))

(defun faithful-hypotheses (wrld ground)
  (list (plist-worldp-with-formals wrld)
        (faithful-known-packages-p wrld)
        (faithful-package-world-p wrld)
        (faithful-constraint-world-p wrld)
        (faithful-fact-world-p wrld)
        (faithful-function-event-world-p wrld)
        (faithful-stobj-program-world-p wrld)
        (faithful-nonprogram-fns-p ground wrld)))

(defmacro faithful-test-world (name wrld)
  (list 'let (list (list 'hypotheses
                        (list 'faithful-hypotheses wrld '(@ faithful-ground-fns))))
        (list 'prog2$
              (list 'cw "~%~s0 hypotheses ~x1~%" name 'hypotheses)
              (list 'faithful-test name
                    '(equal hypotheses '(t t t t t t t t))))))

(faithful-test-world "initial world" (@ faithful-boot-world))
(faithful-test-world "world with hidden packages" (@ faithful-hidden-world))
(faithful-test-world "world with defpun" (@ faithful-defpun-world))
(faithful-test-world "world with alist-equiv" (@ faithful-alist-equiv-world))
(faithful-test-world "world with abstract stobjs" (@ faithful-absstobjs-world))
(faithful-test-world "world with dft-ex" (@ faithful-dft-world))
(faithful-test-world "world with statement and program examples" (@ faithful-sample-world))

; Compare the statement data against the independent world predicates.

(defun faithful-formula-list-from-world-p (pairs args wrld)
  (if (endp pairs)
      t
    (and (faithful-constraint-formula-from-world-p (car pairs) args wrld)
         (faithful-formula-list-from-world-p (cdr pairs) args wrld))))

(defun faithful-test-definition-records-p (defs rulers wrld)
  (if (endp defs)
      t
    (let ((fn (caar defs)))
      (and (not (eq (getprop fn 'formals t 'current-acl2-world wrld) t))
           (getprop fn 'unnormalized-body nil 'current-acl2-world wrld)
           (equal (faithful-ruler-extenders fn wrld) rulers)
           (faithful-test-definition-records-p (cdr defs) rulers wrld)))))

(defun faithful-test-statement-p (line wrld)
  (let ((word (car line))
        (args (cadr line)))
    (case-match word
      ("define"
       (and (faithful-definition-data-p args wrld)
            (faithful-test-definition-records-p (cdr args) (car args) wrld)))
      ("theorem"
       (and (cadr args) (faithful-formula-data-p args wrld)))
      ("axiom"
       (and (cadr args) (faithful-formula-data-p args wrld)))
      ("package" (faithful-package-data-p args wrld))
      ("hidden-package" (faithful-hidden-package-data-p args wrld))
      ("choose" (faithful-choice-data-p args wrld))
      ("constrain"
       (and (faithful-constraint-data-p args wrld)
            (faithful-formula-list-from-world-p (cadr args) args wrld)))
      ("reserve" (faithful-reserve-data-p args wrld))
      (& nil))))

(defun faithful-first-statement-problem (statements wrld)
  (if (endp statements)
      nil
    (if (faithful-test-statement-p (car statements) wrld)
        (faithful-first-statement-problem (cdr statements) wrld)
      (list (caar statements) (caadar statements)))))

(defun faithful-constraint-example-p (statements unknownp wrld)
  (cond ((endp statements) nil)
        ((and (equal (caar statements) "constrain")
              (let* ((fn (caaar (cadar statements)))
                     (owner (faithful-constraint-owner fn wrld)))
                (equal (unknown-constraints-p (faithful-stored-constraint owner wrld))
                       unknownp)))
         t)
        (t (faithful-constraint-example-p (cdr statements) unknownp wrld))))

; Check the statement or diagnostic for every selected signed encapsulate.

(defun faithful-test-constraint-reports-p (events statements notes libraryp wrld)
  (if (endp events)
      t
    (let* ((event (car events))
           (signature (faithful-event-names event)))
      (and (if (and (eq (access-event-tuple-type event) 'encapsulate)
                    (consp signature))
               (let ((owner (faithful-constraint-owner (car signature) wrld)))
                 (or (faithful-constraint-report-present-p :statement owner statements wrld)
                     (faithful-constraint-report-present-p :missing-label owner notes wrld)
                     (and libraryp
                          (member-equal '("note" ("order of the library not completed" nil))
                                        notes))))
             t)
           (faithful-test-constraint-reports-p
            (cdr events) statements notes libraryp wrld)))))

; The supplied translation exercises the input boundary for a program
; function in the startup world that has no stored body.

(assign faithful-program-translations
        '((access-event-tuple-local-p :ok eq (car x) (quote local))))

(defun faithful-first-program-problem (lines translations wrld)
  (if (endp lines)
      nil
    (let* ((line (car lines))
           (word (car line))
           (args (cadr line))
           (matches
            (cond ((equal word "define")
                   (faithful-program-definitions-p (cdr args) translations wrld))
                  ((equal word "attach")
                   (faithful-attachment-data-p args wrld))
                  (t nil))))
      (if matches
          (faithful-first-program-problem (cdr lines) translations wrld)
        (list word (car args))))))

(mv-let (statements program notes)
  (bx-library-lines (@ faithful-ground-fns) (@ faithful-boot-hi)
                    (@ faithful-program-translations) (w state))
  (let* ((wrld (w state))
         (problem (faithful-first-statement-problem statements wrld))
         (program-problem (faithful-first-program-problem
                           program (@ faithful-program-translations) wrld)))
    (prog2$ (cw "~%Library statements ~x0, first mismatch ~x1~%" (len statements) problem)
            (progn$
             (faithful-test "library statement data"
                            (and (not problem)
                                 (subsetp-equal '("define" "theorem" "constrain" "reserve")
                                                (strip-cars statements))
                                 (faithful-constraint-example-p statements t wrld)
                                 (faithful-constraint-example-p statements nil wrld)))
             (faithful-test
              "library constraint outcomes"
              (faithful-test-constraint-reports-p
               (bx-events wrld 0 (@ faithful-boot-hi) nil) statements notes t wrld))
             (cw "~%Library program lines ~x0, first mismatch ~x1~%"
                 (len program) program-problem)
             (faithful-test "library program data"
                            (and (not program-problem)
                                 (member-equal "attach" (strip-cars program))
                                 (not (getprop 'access-event-tuple-local-p
                                               'unnormalized-body nil
                                               'current-acl2-world wrld))
                                 (member-equal
                                  '("define" (nil (access-event-tuple-local-p (x)
                                                    (eq (car x) 'local))))
                                  program)))))))

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-boot-hi)
                 (@ faithful-sample-hi) nil (system-books-dir state) (cbd)
                 (w state))
  (declare (ignore aids))
  (let* ((wrld (w state))
         (problem (faithful-first-statement-problem statements wrld))
         (program-problem (faithful-first-program-problem program nil wrld)))
    (prog2$ (cw "~%Book statements ~x0, first mismatch ~x1~%" (len statements) problem)
            (progn$
             (faithful-test "book statement data"
                            (and (not problem)
                                 (subsetp-equal '("define" "theorem" "axiom" "package"
                                                  "hidden-package" "choose" "constrain"
                                                  "reserve")
                                                (strip-cars statements))))
             (faithful-test
              "book constraint outcomes"
              (faithful-test-constraint-reports-p
               (bx-events wrld (@ faithful-boot-hi) (@ faithful-sample-hi) nil)
               statements notes nil wrld))
             (cw "~%Book program lines ~x0, first mismatch ~x1~%"
                 (len program) program-problem)
             (faithful-test "book program data"
                            (and (not program-problem)
                                 (member-equal "attach" (strip-cars program))
                                 (member-equal
                                  '("define" (nil (faithful-executable-example (x) (cons x x))))
                                  program)))
             (faithful-test "constraint with guard holders"
                            (let* ((formula (getprop 'faithful-guarded-law 'theorem
                                                     nil 'current-acl2-world wrld))
                                   (terms (faithful-stored-constraint 'faithful-guarded wrld)))
                              (and (equal (len terms) 2)
                                   (not (subsetp-equal (flatten-ands-in-lit formula)
                                                       terms))
                                   (equal (faithful-matching-conjuncts formula terms)
                                          terms)
                                   (member-equal
                                    (list "constrain"
                                          (list '((faithful-guarded 1))
                                                (list (list 'faithful-guarded-law formula))))
                                    statements))))))))

