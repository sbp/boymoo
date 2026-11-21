(in-package "ACL2")

(logic)
(set-verify-guards-eagerness 0)

; The test driver projects the declarations used by the order theorem
; directly from spec/ground.txt.

(defun structure-test-select (kind projection)
  (cond ((endp projection) nil)
        ((eq kind (caar projection))
         (cons (cdar projection) (structure-test-select kind (cdr projection))))
        (t (structure-test-select kind (cdr projection)))))

(defun structure-test-ground-definitions (projection)
  (strip-cars (structure-test-select :define projection)))

(defun structure-test-ground-arities (projection)
  (structure-record-signatures
   (structure-declared-signatures
    (append (structure-test-select :primitive projection)
            (structure-test-select :define projection)))
   nil))

(defun structure-test-packages (packages declarations table)
  (if (endp packages)
      table
    (let* ((name (car packages))
           (imports (cadr (assoc-equal name declarations))))
      (structure-test-packages (cdr packages) declarations
                               (structure-record-imports name imports table)))))

(defun structure-test-ground-package-rules (packages)
  (cond ((endp packages) nil)
        ((equal (car packages) "COMMON-LISP")
         (structure-test-ground-package-rules (cdr packages)))
        (t (cons (structure-package-rule (car packages))
                 (structure-test-ground-package-rules (cdr packages))))))

(defun structure-test-same-members-p (a b)
  (and (subsetp-equal a b) (subsetp-equal b a)))

(defun structure-test-imports-match-world-p (declarations)
  (or (endp declarations)
      (and (equal (cadar declarations) (pkg-imports (caar declarations)))
           (structure-test-imports-match-world-p (cdr declarations)))))

(defun structure-test-groundp (projection wrld)
  (let* ((definitions (structure-test-ground-definitions projection))
         (signatures (structure-test-ground-arities projection))
         (package-decls (structure-test-select :package projection))
         (package-names (strip-cars package-decls))
         (packages (structure-test-packages *structure-ground-packages* package-decls
                                            (structure-ground-packages)))
         (rules (append (strip-cars (structure-test-select :axiom projection))
                        (structure-test-ground-package-rules package-names)))
         (names (structure-ground-names definitions)))
    (and (structure-ground-contextp definitions wrld signatures names packages)
         (structure-test-same-members-p package-names *structure-ground-packages*)
         (structure-test-same-members-p
          (append '(t nil) (strip-cars signatures) rules)
          (strip-cars names))
         (structure-test-same-members-p rules *structure-ground-axioms*)
         (structure-test-imports-match-world-p package-decls))))

; Check every record in the independently selected interval.

(defun structure-test-event-hypotheses (records)
  (if (endp records)
      nil
    (let ((record (car records)))
      (or (and (not (structure-namex-shapep record))
               (list :namex (structure-event-number record) (structure-event-kind record)))
          (structure-test-event-hypotheses (cdr records))))))

(defun structure-test-range (wrld lo hi)
  (cond ((not (plist-worldp wrld)) :world-triples)
        ((not (structure-range-recordsp wrld lo hi)) :event-numbers-or-depths)
        (t (structure-test-event-hypotheses (structure-range-events wrld lo hi nil)))))

; When the independent order test passes, any supplied name has at most
; one effective introduction.  Look up supplies in the statements and
; coverage notes for every event name, including names inside constraints.

(defun structure-test-index-names (statements names packages)
  (if (endp statements)
      (mv names packages)
    (let ((line (car statements)))
      (structure-test-index-names (cdr statements)
                                  (structure-record-names (structure-names line) names)
                                  (structure-record-package line packages)))))

(defun structure-test-missing-name (names record symbols packages notes
                                          ground-definitions libraryp wrld)
  (if (endp names)
      nil
    (let ((name (car names)))
      (if (or (structure-no-statement-due-p name record wrld)
              (and libraryp
                   (structure-library-ground-supplies-p name ground-definitions))
              (hons-get name (if (stringp name) packages symbols))
              (structure-name-has-note-p name notes))
          (structure-test-missing-name (cdr names) record symbols packages notes
                                       ground-definitions libraryp wrld)
        (list :missing-name (structure-event-number record)
              (structure-event-kind record) name)))))

(defun structure-test-missing-record (records symbols packages notes
                                             ground-definitions libraryp wrld)
  (and (consp records)
       (or (structure-test-missing-name
            (structure-event-names (car records)) (car records) symbols packages notes
            ground-definitions libraryp wrld)
           (structure-test-missing-record (cdr records) symbols packages notes
                                          ground-definitions libraryp wrld))))

(defun structure-test-first-order-note (notes)
  (cond ((endp notes) nil)
        ((and (equal (caar notes) "note")
              (member-equal (caadar notes)
                            '("line that could not be admitted in order"
                              "library whose lines could not be admitted in order")))
         (cadar notes))
        (t (structure-test-first-order-note (cdr notes)))))

; Check each manufactured formula name against the independent count of
; records that could take it in the two ranges.

(defun structure-test-generated-formula-names (formulas lines records wrld)
  (and (consp formulas)
       (let ((name (caar formulas)))
         (or (and (structure-unregistered-symbol-p name wrld)
                  (not (and (structure-name-source name)
                            (equal (structure-name-opportunities name records wrld) 1)
                            (equal (structure-introduction-count name lines nil) 1)))
                  (list :generated-name name))
             (structure-test-generated-formula-names (cdr formulas) lines records wrld)))))

(defun structure-test-generated-statements (remaining lines records wrld)
  (and (consp remaining)
       (or (and (equal (caar remaining) "constrain")
                (structure-test-generated-formula-names
                 (cadr (cadar remaining)) lines records wrld))
           (structure-test-generated-statements (cdr remaining) lines records wrld))))

(defun structure-test-file (lines notes projection boot-hi lo hi libraryp wrld)
  (let* ((definitions (structure-test-ground-definitions projection))
         (signatures (structure-test-ground-arities projection))
         (names (structure-ground-names definitions))
         (packages (structure-ground-world-packages wrld))
         (records (structure-range-events wrld lo hi nil))
         (prefix-records (if libraryp nil (structure-range-events wrld 0 boot-hi nil)))
         (all-records (append prefix-records records)))
    (or (and (not (structure-test-groundp projection wrld)) :ground)
        (structure-test-first-order-note notes)
        (mv-let (failures remaining-fns remaining-names remaining-packages earlier)
          (structure-order-scan lines signatures names packages nil)
          (declare (ignore remaining-fns remaining-names remaining-packages earlier))
          (and failures (list :statement-order (caar failures) (caadr (car failures)))))
        (and (not (structure-naming-recordsp all-records)) :generated-name-record-shape)
        (and (not (structure-range-recordsp wrld 0 boot-hi)) :generated-name-library-range)
        (structure-test-generated-statements lines lines all-records wrld)
        (mv-let (written-names written-packages)
          (structure-test-index-names lines nil nil)
          (structure-test-missing-record
           records written-names written-packages notes definitions libraryp wrld)))))

(defun structure-test-book (library projection boot-hi lo hi wrld)
  (let ((definitions (structure-test-ground-definitions projection)))
    (or (and (not (< lo hi)) :book-added-no-events)
        (structure-test-range wrld lo hi)
        (and (not (structure-library-prefix-matches-p library definitions boot-hi wrld))
             :library-prefix)
        (mv-let (statements program notes aids)
          (bx-book-lines definitions boot-hi lo hi nil "" "" wrld)
          (declare (ignore program aids))
          (structure-test-file (append library statements) notes
                               projection boot-hi lo hi nil wrld)))))

(defun structure-test-specimen (library projection lo hi specimen-world installed-world)
  (or (structure-test-range specimen-world lo hi)
      (and (not (structure-test-groundp projection specimen-world)) :specimen-ground)
      (structure-test-book library projection lo lo hi installed-world)))

(defun structure-test-result (label failure)
  (if failure
      (cw "~%structure fail ~s0 ~x1~%" label failure)
    (cw "~%structure ok ~s0~%" label)))

; The following property-list worlds exercise specific entry cases.
; Their landmarks are data passed to the exporter.

(defun structure-test-minimal-world (primitives)
  (if (endp primitives)
      '((ttags-seen global-value) (include-book-alist global-value)
        (redef-seen global-value) (event-landmark global-value 0))
    (cons (list* (caar primitives) 'formals (cadar primitives))
          (structure-test-minimal-world (cdr primitives)))))

(defun structure-test-landmark (number depth kind namex class form)
  (list* 'event-landmark 'global-value
         (if (zp depth) number (cons number depth))
         (list* (list kind) namex class)
         form))

(defun structure-test-choice-self-call ()
  (let ((wrld
         (list*
          (structure-test-landmark
           1 0 'defchoose 'structure-example-choice :common-lisp-compliant
           '(defchoose structure-example-choice (x) nil (structure-example-choice)))
          '(structure-example-choice formals)
          '(structure-example-choice defchoose-axiom implies
             (structure-example-choice)
             ((lambda (x) (structure-example-choice)) (structure-example-choice)))
          (structure-test-minimal-world *primitive-formals-and-guards*))))
    (mv-let (statements program notes aids)
      (bx-book-lines nil 0 0 1 nil "" "" wrld)
      (declare (ignore program aids))
      (and (plist-worldp wrld)
           (equal statements
                  '(("choose" (structure-example-choice (x) nil (structure-example-choice) nil))))
           (not (structure-orderp statements nil nil (structure-ground-packages)))
           (equal (structure-test-first-order-note notes)
                  '("line that could not be admitted in order"
                    ((structure-example-choice) nil
                     ((:not-in-use (structure-example-choice))))))))))

(defun structure-test-import-shadowing ()
  (let ((lines '(("package" ("ACL2-PC" (acl2::structure-example-import)))
                 ("theorem"
                  (structure-example-import-theorem
                   (quote acl2-pc::structure-example-import))))))
    (mv-let (notes signatures names packages seen)
      (bx-check-stmts lines nil nil (structure-ground-packages) nil nil)
      (declare (ignore signatures names packages seen))
      (and (equal (bx-select :note notes)
                  '(("line that could not be admitted in order"
                     (nil structure-example-import-theorem
                      ((:name-imported (acl2-pc::structure-example-import)))))))
           (not (structure-orderp lines nil nil (structure-ground-packages)))))))

(defun structure-test-invalid-library ()
  (let ((wrld
         (list*
          (structure-test-landmark
           2 0 'defthm 'structure-example-use :ideal
           '(defthm structure-example-use (structure-example-broken)))
          '(structure-example-use theorem structure-example-broken)
          (structure-test-landmark
           1 0 'defun 'structure-example-broken :common-lisp-compliant
           '(defun structure-example-broken () (structure-example-absent)))
          '(structure-example-broken formals)
          '(structure-example-broken unnormalized-body structure-example-absent)
          (structure-test-minimal-world *primitive-formals-and-guards*))))
    (mv-let (library lib-program lib-notes)
      (bx-library-lines nil 1 nil wrld)
      (declare (ignore lib-program))
      (mv-let (book program notes aids)
        (bx-book-lines nil 1 1 2 nil "" "" wrld)
        (declare (ignore program aids))
        (and (equal library '(("define" (nil (structure-example-broken nil
                                               (structure-example-absent))))))
             (equal book '(("theorem" (structure-example-use (structure-example-broken)))))
             (equal (structure-order-note-count lib-notes) 1)
             (equal (structure-test-first-order-note notes)
                    (list "library whose lines could not be admitted in order"
                          (list (structure-test-first-order-note lib-notes)))))))))

(defun structure-test-reservation-note ()
  (let* ((entry (structure-test-landmark
                 1 0 'table 'structure-example-reservation nil
                 '(table structure-example-reservation)))
         (wrld (list* entry '(structure-example-reservation const . 1)
                      (structure-test-minimal-world *primitive-formals-and-guards*)))
         (name 'structure-example-reservation))
    (mv-let (statements program notes aids)
      (bx-book-lines nil 0 0 1 nil "" "" wrld)
      (declare (ignore program aids))
      (and (plist-worldp wrld)
           (not (structure-no-statement-due-p name (cddr entry) wrld))
           (not (structure-lines-supply-p name statements))
           (structure-notes-report-p name notes)))))

(defun structure-test-unlisted-sibling-note ()
  (let* ((definition (structure-test-landmark
                      1 1 'defun 'structure-example-sibling :common-lisp-compliant
                      '(defun structure-example-sibling () 'nil)))
         (choice (structure-test-landmark
                  2 1 'defchoose 'structure-example-unlisted-choice :common-lisp-compliant
                  '(defchoose structure-example-unlisted-choice (x) nil (equal x 'nil))))
         (wrld
          (list*
           (structure-test-landmark
            3 0 'encapsulate '(structure-example-root) :common-lisp-compliant
            '(encapsulate ((structure-example-root () => *))))
           choice
           definition
           '(structure-example-root formals)
           '(structure-example-root constraint-lst-etc nil)
           '(structure-example-sibling formals)
           '(structure-example-sibling unnormalized-body quote nil)
           '(structure-example-sibling constraint-lst-etc structure-example-root)
           '(structure-example-unlisted-choice formals)
           '(structure-example-unlisted-choice constraint-lst-etc structure-example-root)
           (structure-test-minimal-world *primitive-formals-and-guards*)))
         (name 'structure-example-sibling)
         (choice-name 'structure-example-unlisted-choice))
    (mv-let (statements program notes aids)
      (bx-book-lines nil 0 0 3 nil "" "" wrld)
      (declare (ignore program aids))
      (and (plist-worldp wrld)
           (not (structure-lines-supply-p name statements))
           (not (structure-lines-supply-p choice-name statements))
           (structure-notes-report-p name notes)
           (structure-notes-report-p choice-name notes)))))

(defun structure-test-nonground-axiom ()
  (let* ((entry (structure-test-landmark
                 2 0 'defaxiom 'structure-example-axiom :ideal
                 '(defaxiom structure-example-axiom 't)))
         (ground-entry (structure-test-landmark
                        1 0 'defaxiom 'car-cons :ideal '(defaxiom car-cons 't)))
         (wrld (list* entry '(structure-example-axiom theorem quote t)
                      ground-entry '(car-cons theorem quote t)
                      (structure-test-minimal-world *primitive-formals-and-guards*))))
    (mv-let (statements program notes)
      (bx-library-lines nil 2 nil wrld)
      (declare (ignore program))
      (and (plist-worldp wrld)
           (equal statements '(("axiom" (structure-example-axiom (quote t)))))
           (equal (structure-order-note-count notes) 0)))))

; Exercise exact repeats, conflicting statements and the hidden to open
; transition, using the branch that prints a name in an order note.

(defun structure-test-repeat-cases ()
  (let* ((line '("reserve" (structure-example-repeat)))
         (conflict '("theorem" (structure-example-repeat (quote t))))
         (name 'structure-example-repeat)
         (packages (structure-ground-packages))
         (hidden '("hidden-package" ("STRUCTURE-EXAMPLE" nil)))
         (open '("package" ("STRUCTURE-EXAMPLE" nil))))
    (mv-let (notes signatures names declared seen)
      (bx-check-stmts (list line line) nil nil packages nil nil)
      (declare (ignore signatures names declared seen))
      (mv-let (conflicts signatures names declared seen)
        (bx-check-stmts (list line line conflict) nil nil packages nil nil)
        (declare (ignore signatures names declared seen))
        (and (not notes)
             (equal (structure-introduction-count name (list line line) nil) 1)
             (equal (structure-introduction-count name (list line line conflict) nil) 2)
             (structure-order-notes-report-conflict-p
              name (bx-note-lines (bx-select :note conflicts)))
             (equal (structure-introduction-count "STRUCTURE-EXAMPLE"
                                                  (list hidden open open) nil)
                    1)
             (equal (structure-introduction-count 'structure-example-package
                                                  (list hidden open open) nil)
                    1)
             (structure-orderp (list hidden open open) nil nil packages))))))


; Keep the actual startup library for a fresh session that includes a
; sample book before the proof support books.

(defun structure-test-write-library (lines file state)
  (declare (xargs :stobjs state))
  (mv-let (channel state)
    (open-output-channel file :object state)
    (if channel
        (pprogn (print-object$+ lines channel :serialize-character #\Z)
                (close-output-channel channel state)
                (value :structure-library-written))
      (er soft 'structure-test-write-library "Cannot write ~x0." file))))

(defun structure-test-read-library (file state)
  (declare (xargs :stobjs state))
  (mv-let (channel state)
    (open-input-channel file :object state)
    (if channel
        (mv-let (eof lines state)
          (read-object channel state)
          (pprogn (close-input-channel channel state)
                  (if eof
                      (er soft 'structure-test-read-library "Empty object file ~x0." file)
                    (value lines))))
      (er soft 'structure-test-read-library "Cannot read ~x0." file))))

(defun structure-test-cross-file-repeat ()
  (let* ((name 'structure-example-cross-file)
         (form (list 'deflabel name))
         (wrld (list* (structure-test-landmark 2 0 'deflabel name :program form)
                      (structure-test-landmark 1 0 'deflabel name :program form)
                      '(structure-example-cross-file label . t)
                      (structure-test-minimal-world *primitive-formals-and-guards*))))
    (mv-let (library library-program library-notes)
      (bx-library-lines nil 1 nil wrld)
      (declare (ignore library-program library-notes))
      (mv-let (book program notes aids)
        (bx-book-lines nil 1 1 2 nil "" "" wrld)
        (declare (ignore program aids))
        (and (equal library '(("reserve" (structure-example-cross-file))))
             (equal book library)
             (equal (bm-line (caar book) (cadar book))
                    (bm-line (caar library) (cadar library)))
             (equal (structure-introduction-count name book library) 0)
             (equal (structure-introduction-count name (append library book) nil) 1)
             (not (posp (structure-order-note-count notes))))))))

(defun structure-test-named-conversion-note ()
  (let* ((name 'structure-example-unsupported-choice)
         (wrld (list* (structure-test-landmark
                       1 0 'defchoose name :common-lisp-compliant
                       (list 'defchoose name '(x) nil '(quote t)))
                      '(structure-example-unsupported-choice formals)
                      '(structure-example-unsupported-choice defchoose-axiom quote t)
                      (structure-test-minimal-world *primitive-formals-and-guards*))))
    (mv-let (statements program notes aids)
      (bx-book-lines nil 0 0 1 nil "" "" wrld)
      (declare (ignore program aids))
      (and (not (structure-lines-supply-p name statements))
           (structure-notes-report-p name notes)))))

; A library conflict is carried in a book's notes, even when the book
; itself only repeats a line.

(defun structure-test-library-name-conflict ()
  (let* ((name 'structure-example-conflict)
         (label (list 'deflabel name))
         (wrld (list* (structure-test-landmark 3 0 'deflabel name :program label)
                      (structure-test-landmark 2 0 'deflabel name :program label)
                      (structure-test-landmark 1 0 'defthm name :ideal (list 'defthm name ''t))
                      '(structure-example-conflict label . t)
                      '(structure-example-conflict theorem quote t)
                      (structure-test-minimal-world *primitive-formals-and-guards*))))
    (mv-let (library lib-program lib-notes)
      (bx-library-lines nil 2 nil wrld)
      (declare (ignore lib-program lib-notes))
      (mv-let (book program notes aids)
        (bx-book-lines nil 2 2 3 nil "" "" wrld)
        (declare (ignore program aids))
        (and (equal book '(("reserve" (structure-example-conflict))))
             (equal (structure-introduction-count name (append library book) nil) 2)
             (equal (structure-order-note-count notes) 1)
             (structure-order-notes-report-conflict-p name notes))))))

; The event for G calls a constrained F.  The one for H calls G and
; thus waits for the same constraint to be emitted.

(defun structure-test-encapsulate-order ()
  (let* ((wrld (list*
                (structure-test-landmark
                 3 0 'encapsulate '(structure-example-f) :common-lisp-compliant
                 '(encapsulate ((structure-example-f () => *))))
                (structure-test-landmark
                 2 1 'defun 'structure-example-h :common-lisp-compliant
                 '(defun structure-example-h () (structure-example-g)))
                (structure-test-landmark
                 1 1 'defun 'structure-example-g :common-lisp-compliant
                 '(defun structure-example-g () (structure-example-f)))
                '(structure-example-f formals)
                '(structure-example-f constraint-lst-etc nil)
                '(structure-example-f siblings structure-example-f)
                '(structure-example-g formals)
                '(structure-example-g unnormalized-body structure-example-f)
                '(structure-example-h formals)
                '(structure-example-h unnormalized-body structure-example-g)
                (structure-test-minimal-world *primitive-formals-and-guards*)))
         (expected '(("constrain" (((structure-example-f 0)) nil))
                     ("define" (nil (structure-example-g nil (structure-example-f))))
                     ("define" (nil (structure-example-h nil (structure-example-g)))))))
    (mv-let (library lib-program lib-notes)
      (bx-library-lines nil 3 nil wrld)
      (declare (ignore lib-program))
      (mv-let (book program notes aids)
        (bx-book-lines nil 0 0 3 nil "" "" wrld)
        (declare (ignore program aids))
        (and (equal book expected)
             (equal library expected)
             (equal (structure-order-note-count lib-notes) 0)
             (equal (structure-order-note-count notes) 0))))))

(defun structure-test-examples ()
  (progn$
   (structure-test-result "repeat-cases" (not (structure-test-repeat-cases)))
   (structure-test-result "cross-file-repeat" (not (structure-test-cross-file-repeat)))
   (structure-test-result "named-conversion-note" (not (structure-test-named-conversion-note)))
   (structure-test-result "choice-self-call" (not (structure-test-choice-self-call)))
   (structure-test-result "import-shadowing" (not (structure-test-import-shadowing)))
   (structure-test-result "invalid-library" (not (structure-test-invalid-library)))
   (structure-test-result "library-name-conflict" (not (structure-test-library-name-conflict)))
   (structure-test-result "reservation-note" (not (structure-test-reservation-note)))
   (structure-test-result "unlisted-sibling-note" (not (structure-test-unlisted-sibling-note)))
   (structure-test-result "nonground-axiom" (not (structure-test-nonground-axiom)))
   (structure-test-result "encapsulate-order" (not (structure-test-encapsulate-order)))))
